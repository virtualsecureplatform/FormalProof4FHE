module
public import FormalProof4FHE.HasteBoots.RetainedPaddedExtraction
public import FormalProof4FHE.HasteBoots.KeySwitchPaddedExtraction
@[expose] public section

/-! Accepted canonical key-switch output failure and the actual reached
extraction risk, stated independently of component support proofs. -/
namespace FormalProof4FHE.HasteBoots.RetainedCanonicalOutput
noncomputable section
variable {q c lanes dimension levels : ℕ} [Fact q.Prime]
  {Before Cfg Input Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq NativeRootMessage.Digest] {H : Cfg → ℕ}
variable (base : Before → Memory → KeySwitchPaddedExtraction.Scheme (q := q) (c := c) (lanes := lanes)
  (Input := Input) (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (heights := H))

/-- Only a returned, accepted extraction with an incorrect caller output counts.
Skipped and rejected continuations contribute no failure. -/
def Wrong (bits : ℕ) (shape : dimension ≤ 2^(c+lanes))
    (original : NativeKeySwitch.Key q (2^(c+lanes)) levels)
    (output : NativePublic.Ciphertext q dimension)
    (endpoint : Before → NativeBlindRotation.Cipher q (2^(c+lanes)))
    (outcome : Before × Option (Sigma (RetainedPaddedExtraction.Child base))) : Prop :=
  ∃ child, outcome.2 = some child ∧
    PaddedPublicZeroCheck.accepted (base child.1.1 child.1.2) child.2.2.1 = true ∧
    output ≠ NativeKeySwitch.extract shape
      (CanonicalKeySwitch.switch bits original (NativePBS.bias (endpoint child.1.1)))

/-- The original-owner extraction risk of the literal returned child. -/
def Risk (dummy : NativeRootMessage.Digest)
    (capacity : ∀ before memory factor, 2^((base before memory).code factor).suffix ≤
      ((base before memory).code factor).m*(2^lanes))
    (radius : Before → Memory → Unit → ℕ)
    (outcome : Before × Option (Sigma (RetainedPaddedExtraction.Child base))) : Prop :=
  ∃ child, outcome.2 = some child ∧
    PaddedPublicZeroCheck.OriginalRisk (base child.1.1 child.1.2) dummy
      (capacity child.1.1 child.1.2) (radius child.1.1 child.1.2) child.2

open OracleSpec OracleComp

omit [DecidableEq NativeRootMessage.Digest] in
/-- Separate one final exception from the remaining safe output event. -/
theorem split_bad {Result : Type} (experiment : ProbComp Result) (wrong bad : Result → Prop) :
    Pr{let result ← experiment}[wrong result] ≤
      Pr{let result ← experiment}[bad result] +
        Pr{let result ← experiment}[wrong result ∧ ¬bad result] := by
  apply le_trans (prEvent_mono experiment wrong (fun result => bad result ∨ (wrong result ∧ ¬bad result)) ?_)
    (prEvent_or_le experiment bad (fun result => wrong result ∧ ¬bad result))
  intro result failed
  classical
  by_cases exceptional : bad result
  · exact Or.inl exceptional
  · exact Or.inr ⟨failed,exceptional⟩

omit [DecidableEq NativeRootMessage.Digest] in
/-- Add the one exception probability to a proved safe-event bound. -/
theorem bound_with_bad {Result : Type} (experiment : ProbComp Result) (wrong bad : Result → Prop)
    (rate : ENNReal)
    (safe : Pr{let result ← experiment}[wrong result ∧ ¬bad result] ≤ rate) :
    Pr{let result ← experiment}[wrong result] ≤ Pr{let result ← experiment}[bad result] + rate :=
  (split_bad experiment wrong bad).trans (add_le_add le_rfl safe)

end
end FormalProof4FHE.HasteBoots.RetainedCanonicalOutput
