module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsOpeningChecks

@[expose] public section

/-! Native single-opening suffix/claim enforcement. Serialized claims retain
their original words; the final vector comparison uses field equality. The
check computes the suffix fold, never accepts a supplied finished vector. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsClaim

open NativeFieldRepresentation (GoldWord goldCanonical goldValue)
open NativeGoldPcsWire (Query)
open NativeLookupRequestWire (Row)
open NativeBrakedownContext (Parameters)

def equal (left right : List GoldWord) : Bool := decide (left.map goldCanonical = right.map goldCanonical)

inductive Error where
  | finish | claim
  deriving DecidableEq

def verify {C : Type} (parameters : Parameters C) (query : Query) (response : List GoldWord) (claimed : Row) : Except Error Unit :=
  match NativeGoldPcsArithmetic.finish parameters.numVariables.val parameters.width.val parameters.leftVariables.val query.models response with
  | none => .error .finish
  | some result => if equal result claimed.val then .ok () else .error .claim

noncomputable section

theorem equal_iff (left right : List GoldWord) : equal left right = true ↔ left.map goldValue = right.map goldValue := by
  rw [equal,decide_eq_true_eq,NativeGoldPackedFold.canonical_map_eq_iff]

theorem accepted_iff {C : Type} (parameters : Parameters C) (query : Query) (response : List GoldWord) (claimed : Row) :
    verify parameters query response claimed = .ok () ↔
      ∃ result, NativeGoldPcsArithmetic.finish parameters.numVariables.val parameters.width.val parameters.leftVariables.val query.models response = some result ∧
        result.map goldValue = claimed.val.map goldValue := by
  unfold verify
  cases read : NativeGoldPcsArithmetic.finish parameters.numVariables.val parameters.width.val parameters.leftVariables.val query.models response with
  | none => simp
  | some result =>
    dsimp only
    by_cases same : equal result claimed.val = true
    · rw [ite_eq_left same]
      constructor
      · intro _
        exact ⟨result,rfl,(equal_iff _ _).mp same⟩
      · intro _; rfl
    · rw [ite_eq_right same]
      constructor
      · intro impossible; contradiction
      · rintro ⟨other,eq,values⟩
        cases eq
        exact False.elim (same ((equal_iff _ _).mpr values))

/-- Enforced claims are exactly the semantic native suffix fold of the
original response, including the native constant-lane shortcut. -/
theorem accepted_value {C : Type} (parameters : Parameters C) (query : Query) (response : List GoldWord) (claimed : Row)
    (valid : NativeGoldMatrixWeights.QueryValid parameters.width.val query.models)
    (accepted : verify parameters query response claimed = .ok ()) :
    claimed.val.map goldValue = List.ofFn (FlatMatrixFold.foldAll
      ((query.models.drop parameters.leftVariables.val).map (NativeGoldPackedMeaning.pairValue parameters.width.val))
      (fun index lane => goldValue (response[lane.val*2^(parameters.numVariables.val-parameters.leftVariables.val)+index.val]?.getD 0))) := by
  obtain ⟨result,read,same⟩ := (accepted_iff parameters query response claimed).mp accepted
  exact same.symm.trans (NativeGoldPcsArithmetic.finish_value _ _ _ _ _ _ valid read)

end
end FormalProof4FHE.HasteBoots.NativeGoldPcsClaim
