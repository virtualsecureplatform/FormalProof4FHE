module

public import FormalProof4FHE.HasteBoots.NativeColumnLayout

@[expose] public section

/-!
# Native batch coordinate checks on one authenticated column family

One random-test response and all grouped structured responses use the same
received column payloads. The loop checks the random test once per coordinate,
then all groups, including the empty-group boundary. Checking zero groups does
not erase the independent random-test obligation. Authentication is supplied
by the actual worker pool, not assumed here.
-/

namespace FormalProof4FHE.HasteBoots.BatchColumnChecks

variable {F Digest : Type} [Field F] [DecidableEq F]
  {width rows block height groups : ℕ}

def allCoordinates (columns : List (NativeColumnLayout.Column F Digest height rows block))
    (testWeights : Fin (width * rows) → F) (structuredWeights : Fin groups → Fin (width * rows) → F)
    (testResponse : Fin (width * ((2 ^ height) * block)) → F)
    (structuredResponse : Fin groups → Fin (width * ((2 ^ height) * block)) → F) : Bool :=
  columns.all fun column =>
    (List.ofFn fun lane : Fin width =>
      (List.ofFn fun coordinate : Fin block =>
        decide (NativeColumnLayout.dot testWeights column.values lane coordinate =
          testResponse (NativeColumnLayout.responseAddress lane column.position coordinate)) &&
        (List.ofFn fun group : Fin groups =>
          decide (NativeColumnLayout.dot (structuredWeights group) column.values lane coordinate =
            structuredResponse group (NativeColumnLayout.responseAddress lane column.position coordinate))).all id).all id).all id

theorem allCoordinates_iff (columns : List (NativeColumnLayout.Column F Digest height rows block))
    (testWeights : Fin (width * rows) → F) (structuredWeights : Fin groups → Fin (width * rows) → F)
    (testResponse : Fin (width * ((2 ^ height) * block)) → F)
    (structuredResponse : Fin groups → Fin (width * ((2 ^ height) * block)) → F) :
    allCoordinates columns testWeights structuredWeights testResponse structuredResponse = true ↔
      NativeColumnLayout.Checks columns testWeights testResponse ∧
      ∀ group, NativeColumnLayout.Checks columns (structuredWeights group) (structuredResponse group) := by
  simp only [allCoordinates, List.all_eq_true, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, id_eq,
    Bool.and_eq_true_iff, decide_eq_true_eq]
  constructor
  · intro checked
    exact ⟨fun column member lane coordinate => (checked column member lane coordinate).1,
      fun group column member lane coordinate => (checked column member lane coordinate).2 group⟩
  · intro checked column member lane coordinate
    exact ⟨checked.1 column member lane coordinate, fun group => checked.2 group column member lane coordinate⟩

/-- Every grouped response satisfies the existing two-family coordinate
interface with this same random test and these same authenticated payloads. -/
theorem pair_coordinates (columns : List (NativeColumnLayout.Column F Digest height rows block))
    (testWeights : Fin (width * rows) → F) (structuredWeights : Fin groups → Fin (width * rows) → F)
    (testResponse : Fin (width * ((2 ^ height) * block)) → F)
    (structuredResponse : Fin groups → Fin (width * ((2 ^ height) * block)) → F)
    (checked : allCoordinates columns testWeights structuredWeights testResponse structuredResponse = true) (group : Fin groups) :
    NativeColumnLayout.allCoordinates columns testWeights (structuredWeights group) testResponse (structuredResponse group) = true := by
  have checks := (allCoordinates_iff columns testWeights structuredWeights testResponse structuredResponse).mp checked
  exact (NativeColumnLayout.allCoordinates_eq_true_iff columns testWeights (structuredWeights group) testResponse
    (structuredResponse group)).mpr ⟨checks.1, checks.2 group⟩

end FormalProof4FHE.HasteBoots.BatchColumnChecks
