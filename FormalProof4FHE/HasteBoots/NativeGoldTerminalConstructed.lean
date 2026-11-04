module

public import FormalProof4FHE.HasteBoots.NativeGoldTerminalQueryMeaning

@[expose] public section

/-!
# Actual scalar-query construction through the terminal guard

The pulled query is constructed from the same original point used by the
literal terminal program. Its field meaning and all used-vector failures
are derived from the checked constructor and decoder. Matched typed source
inputs then expose either the truthful source terminal or a wrong original
source opening. Accepted PCS authentication, caller count/point geometry,
helper authentication and instruction refinement remain separate obligations.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldTerminalConstructed

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeUsizeMessage (Usize)
open scoped BigOperators

noncomputable section

def pulled {padding : ℕ} (sourceVars : ℕ) (point : List Word)
    (accepted : NativeScalarQueryShape.check sourceVars (3 + padding) point.length = true) :
    ExtensionQuery.Broadcast Goldilocks (3 + padding) sourceVars :=
  ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ accepted)
    (NativeGoldScalarQueryMeaning.fullPoint sourceVars point accepted)

def sourceTruth {padding : ℕ} (sourceVars : ℕ) (point : List Word)
    (accepted : NativeScalarQueryShape.check sourceVars (3 + padding) point.length = true)
    (table : MatrixFold.Cube sourceVars → Fin (3 + padding) → Goldilocks) : Goldilocks3 :=
  ExtensionLookupTerminal.sourceTruth (NativeScalarQueryShape.checked_power _ _ _ accepted)
    (NativeGoldScalarQueryMeaning.fullPoint sourceVars point accepted) table

/-- No independent query, split coordinates or decoded-source certificate is
supplied: the complete partial field terminal uses the actual constructor. -/
theorem constructedCheck_iff {padding pointVars : ℕ} (sourceVars : ℕ) (eqPoint point : Fin pointVars → Word)
    (accepted : NativeScalarQueryShape.check sourceVars (3 + padding) (List.ofFn point).length = true)
    (count : Usize) (shift : pointVars < 64) (enough : count.val ≤ 2 ^ pointVars)
    (r : Word) (sources : List (List GoldWord)) (powers : List Word) (helper expected : Word) :
    NativeGoldTerminalQuery.constructedCheck sourceVars (3 + padding) (List.ofFn eqPoint) (List.ofFn point)
      count r sources powers helper expected = some true ↔
        NativeGoldTerminalQueryMeaning.value (pulled sourceVars (List.ofFn point) accepted)
          eqPoint point count enough r sources powers helper = some (goldExtensionValue expected) := by
  have interpreted := NativeGoldScalarQueryMeaning.scalarQuery_sourceQuery sourceVars (List.ofFn point) accepted
  rw [NativeGoldScalarQuery.scalarQuery_success _ _ _ accepted, Option.bind_some] at interpreted
  rw [NativeGoldTerminalQuery.constructedCheck, NativeGoldScalarQuery.scalarQuery_success _ _ _ accepted, Option.bind_some]
  exact NativeGoldTerminalQueryMeaning.check_iff _ _ interpreted eqPoint point count shift enough r sources powers helper expected
    ((NativeGoldProjection.dimensions_iff _).mp (NativeScalarQueryShape.checked_dimensions _ _ _ accepted)).2

/-- Field decoding of a truthful original scalar-root opening is derived
from the same constructed source query. PCS acceptance has not supplied it yet. -/
theorem source_truth {padding : ℕ} (sourceVars : ℕ) (point : List Word)
    (accepted : NativeScalarQueryShape.check sourceVars (3 + padding) point.length = true)
    (input : Fin (3 + padding) → GoldWord) (table : MatrixFold.Cube sourceVars → Fin (3 + padding) → Goldilocks)
    (correct : (fun i => goldValue (input i)) = (pulled sourceVars point accepted).query.fold table) :
    NativeGoldTerminalQueryMeaning.source (pulled sourceVars point accepted) (List.ofFn input) =
      some (sourceTruth sourceVars point accepted table) := by
  rw [NativeGoldTerminalQueryMeaning.source_ofFn, correct, ← ExtensionQuery.Broadcast.evaluate, pulled,
    ExtensionLookupTerminal.source_evaluate, PaddedExtension.element_encode]
  rfl

/-- All source slots and weights are matched; no zip omission is assumed away.
The truthful-opening premises are over every original source lane. -/
theorem constructedCheck_truthful_iff {padding pointVars sourceCount : ℕ} (sourceVars : ℕ)
    (eqPoint point : Fin pointVars → Word)
    (accepted : NativeScalarQueryShape.check sourceVars (3 + padding) (List.ofFn point).length = true)
    (count : Usize) (shift : pointVars < 64) (enough : count.val ≤ 2 ^ pointVars)
    (r : Word) (inputs : Fin sourceCount → Fin (3 + padding) → GoldWord) (powers : Fin sourceCount → Word)
    (tables : Fin sourceCount → MatrixFold.Cube sourceVars → Fin (3 + padding) → Goldilocks) (helper expected : Word)
    (correct : ∀ i, (fun lane => goldValue (inputs i lane)) =
      (pulled sourceVars (List.ofFn point) accepted).query.fold (tables i)) :
    NativeGoldTerminalQuery.constructedCheck sourceVars (3 + padding) (List.ofFn eqPoint) (List.ofFn point) count r
      (List.ofFn (fun i => List.ofFn (inputs i))) (List.ofFn powers) helper expected = some true ↔
        ExtensionLookupIdentity.terminal (fun i => goldExtensionValue (eqPoint i)) (fun i => goldExtensionValue (point i))
          (goldExtensionValue r) (∑ i : Fin sourceCount, goldExtensionValue (powers i) *
            sourceTruth sourceVars (List.ofFn point) accepted (tables i))
          (goldExtensionValue helper) count.val enough = goldExtensionValue expected := by
  rw [constructedCheck_iff sourceVars eqPoint point accepted count shift enough]
  rw [NativeGoldTerminalQueryMeaning.value,
    NativeGoldTerminalQueryMeaning.compress_ofFn _ inputs powers _
      (fun i => source_truth sourceVars (List.ofFn point) accepted (inputs i) (tables i) (correct i)),
    Option.map_some, Option.some.injEq]

/-- An accepting actual terminal either has its truthful source expression or
exposes a wrong original-root opening. Helper authentication is still separate. -/
theorem constructedCheck_truthful_or_wrong {padding pointVars sourceCount : ℕ} (sourceVars : ℕ)
    (eqPoint point : Fin pointVars → Word)
    (accepted : NativeScalarQueryShape.check sourceVars (3 + padding) (List.ofFn point).length = true)
    (count : Usize) (shift : pointVars < 64) (enough : count.val ≤ 2 ^ pointVars)
    (r : Word) (inputs : Fin sourceCount → Fin (3 + padding) → GoldWord) (powers : Fin sourceCount → Word)
    (tables : Fin sourceCount → MatrixFold.Cube sourceVars → Fin (3 + padding) → Goldilocks) (helper expected : Word)
    (passed : NativeGoldTerminalQuery.constructedCheck sourceVars (3 + padding) (List.ofFn eqPoint) (List.ofFn point) count r
      (List.ofFn (fun i => List.ofFn (inputs i))) (List.ofFn powers) helper expected = some true) :
    ExtensionLookupIdentity.terminal (fun i => goldExtensionValue (eqPoint i)) (fun i => goldExtensionValue (point i))
      (goldExtensionValue r) (∑ i : Fin sourceCount, goldExtensionValue (powers i) *
        sourceTruth sourceVars (List.ofFn point) accepted (tables i))
      (goldExtensionValue helper) count.val enough = goldExtensionValue expected ∨
      ∃ i, (fun lane => goldValue (inputs i lane)) ≠
        (pulled sourceVars (List.ofFn point) accepted).query.fold (tables i) := by
  classical
  by_cases wrong : ∃ i, (fun lane => goldValue (inputs i lane)) ≠
      (pulled sourceVars (List.ofFn point) accepted).query.fold (tables i)
  · exact Or.inr wrong
  · have correct (i : Fin sourceCount) : (fun lane => goldValue (inputs i lane)) =
        (pulled sourceVars (List.ofFn point) accepted).query.fold (tables i) := by
      by_contra bad
      exact wrong ⟨i, bad⟩
    exact Or.inl ((constructedCheck_truthful_iff sourceVars eqPoint point accepted count shift enough r inputs powers tables helper expected correct).mp passed)

end

end FormalProof4FHE.HasteBoots.NativeGoldTerminalConstructed
