module
public import FormalProof4FHE.HasteBoots.ScalarCompletedChallenge
public import FormalProof4FHE.HasteBoots.ScalarSourcePolynomial
@[expose] public section

/-! A fixed false original equation remains false along the actual native
completed-round chain unless a completed round changes false to true. No
separate claim trace, challenge sequence or received polynomial is supplied. -/
namespace FormalProof4FHE.HasteBoots.ScalarChainHealing
open NativeScalarBatchWire (Statement)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (CompletedRound)
open NativeGoldExtensionArithmetic (Word)
open NativeExtensionFields (Goldilocks3)
open NativeFieldWire (goldExtensionValue)
noncomputable section

/-- Missing getters remain explicit; production slot bounds follow from the
actual native statement and chain count invariants. -/
def value (slot : ℕ) (values : List Word) : Option Goldilocks3 := values[slot]?.map goldExtensionValue

def Healing (truth : List Word → Goldilocks3) (slot : ℕ) (before : List CompletedRound) (entry : CompletedRound) : Prop :=
  value slot entry.priorExpected ≠ some (truth (before.map (fun item => item.challenge))) ∧
    value slot entry.expected = some (truth (before.map (fun item => item.challenge) ++ [entry.challenge]))

/-- One original false equation suffices; no union over all batch equations
is used in this deterministic chain argument. -/
theorem false_or_healing (statement : Statement) (proof : Proof) (entries : List CompletedRound) (expected : List Word)
    (chain : NativeScalarBatchHistory.Chain statement proof entries expected)
    (truth : List Word → Goldilocks3) (slot : ℕ)
    (initial : value slot statement.claims.val ≠ some (truth [])) :
    value slot expected ≠ some (truth (entries.map (fun item => item.challenge))) ∨
      ∃ before entry after, entries = before ++ entry :: after ∧ Healing truth slot before entry := by
  induction chain with
  | nil => exact Or.inl initial
  | @snoc prior expected entry earlier input ordinal source valid ih =>
    rcases ih with falsePrior | healed
    · by_cases falseNext : value slot entry.expected ≠ some (truth ((prior ++ [entry]).map (fun item => item.challenge)))
      · exact Or.inl falseNext
      · have equal : value slot entry.expected = some (truth ((prior ++ [entry]).map (fun item => item.challenge))) := not_ne_iff.mp falseNext
        refine Or.inr ⟨prior,entry,[],by simp,?_,?_⟩
        · rw [input]; exact falsePrior
        · simpa only [List.map_append,List.map_cons,List.map_nil] using equal
    · obtain ⟨before,old,after,parts,healing⟩ := healed
      refine Or.inr ⟨before,old,after ++ [entry],?_,healing⟩
      rw [parts,List.append_assoc,List.cons_append]

theorem terminal_true_has_healing (statement : Statement) (proof : Proof) (entries : List CompletedRound) (expected : List Word)
    (chain : NativeScalarBatchHistory.Chain statement proof entries expected)
    (truth : List Word → Goldilocks3) (slot : ℕ)
    (initial : value slot statement.claims.val ≠ some (truth []))
    (terminal : value slot expected = some (truth (entries.map (fun item => item.challenge)))) :
    ∃ before entry after, entries = before ++ entry :: after ∧ Healing truth slot before entry :=
  (false_or_healing statement proof entries expected chain truth slot initial).resolve_left (fun falseFinal => falseFinal terminal)

/-- No completed healing event leaves a false terminal equation, with the
original common point read from the actual completed native records. -/
theorem no_healing (statement : Statement) (proof : Proof) (entries : List CompletedRound) (expected : List Word)
    (chain : NativeScalarBatchHistory.Chain statement proof entries expected)
    (truth : List Word → Goldilocks3) (slot : ℕ)
    (initial : value slot statement.claims.val ≠ some (truth []))
    (excluded : ∀ before entry after, entries = before ++ entry :: after → ¬ Healing truth slot before entry) :
    value slot expected ≠ some (truth (entries.map (fun item => item.challenge))) := by
  rcases false_or_healing statement proof entries expected chain truth slot initial with stillFalse | healed
  · exact stillFalse
  · obtain ⟨before,entry,after,parts,healing⟩ := healed
    exact False.elim (excluded before entry after parts healing)

end
end FormalProof4FHE.HasteBoots.ScalarChainHealing
