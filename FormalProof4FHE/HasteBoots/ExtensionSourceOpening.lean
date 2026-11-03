module

public import FormalProof4FHE.HasteBoots.ExtensionQuery
public import FormalProof4FHE.HasteBoots.SubclaimSourceLayout

@[expose] public section

/-!
# Extension claims and the existing original-root PCS bad event

The source is exactly the query-independent common-source decoder used by
base-field PCS. Finishing the returned base message, applying the local
post-map and checking its extension value cannot accept an incorrect value
unless that base message has the existing incorrect-evaluation event.
The trusted layout, root, available word and source decoder are unchanged.
This deterministic adapter does not assume a separate extension-field PCS
certificate or discharge the actual lookup stage's probabilistic composition.
-/

namespace FormalProof4FHE.HasteBoots.ExtensionSourceOpening

noncomputable section

variable {F K Position : Type} [Field F] [Field K] [Algebra F K]
  [Fintype Position] [DecidableEq F] {d padding front suffix m : ℕ}

/-- Transfer to the literal matrix-response event already bounded by PCS. -/
theorem false_finish (basis : Module.Basis (Fin d) F K)
    (domain : Position ↪ F) (capacity : 2 ^ suffix ≤ m * (d + padding)) (radius : ℕ)
    (word : Position → (Fin (2 ^ front) × Fin (d + padding)) → Fin (d + padding) → F)
    (query : ExtensionQuery.Broadcast F (d + padding) (front + suffix))
    (messages : Fin (d + padding) → Fin (2 ^ suffix) → F) (truth expected : K)
    (semantics : query.evaluate (SubclaimSourceLayout.decodedSource domain capacity radius word) =
      PaddedExtension.encode basis truth)
    (accepted : PaddedExtension.element basis
      (query.finish (MatrixResponse.finishMessage (SubclaimSourceLayout.rightWeights query.query) messages)) = some expected)
    (wrong : expected ≠ truth) :
    MatrixResponse.finishMessage (SubclaimSourceLayout.rightWeights query.query) messages ≠
      matrixEvaluation (SubclaimSourceLayout.leftWeights query.query) (SubclaimSourceLayout.rightWeights query.query)
        (MatrixOpeningSecurity.extract domain capacity radius word) := by
  rw [← SubclaimSourceLayout.fold_decodedSource]
  exact ExtensionQuery.false_claim basis query _ truth expected _ semantics accepted wrong

theorem coefficients_false_finish (basis : Module.Basis (Fin d) F K)
    (domain : Position ↪ F) (capacity : 2 ^ suffix ≤ m * (d + padding)) (radius : ℕ)
    (word : Position → (Fin (2 ^ front) × Fin (d + padding)) → Fin (d + padding) → F)
    (point : Fin (front + suffix) → K) (messages : Fin (d + padding) → Fin (2 ^ suffix) → F) (expected : K)
    (accepted : PaddedExtension.element basis
      ((ExtensionQuery.coefficientsQuery basis point).finish
        (MatrixResponse.finishMessage (SubclaimSourceLayout.rightWeights (ExtensionQuery.coefficients basis _ point)) messages)) =
          some expected)
    (wrong : expected ≠ ExtensionQuery.evaluate (front + suffix) point
      (fun cell => PaddedExtension.decode basis (SubclaimSourceLayout.decodedSource domain capacity radius word cell))) :
    MatrixResponse.finishMessage (SubclaimSourceLayout.rightWeights (ExtensionQuery.coefficients basis _ point)) messages ≠
      matrixEvaluation (SubclaimSourceLayout.leftWeights (ExtensionQuery.coefficients basis _ point))
        (SubclaimSourceLayout.rightWeights (ExtensionQuery.coefficients basis _ point))
        (MatrixOpeningSecurity.extract domain capacity radius word) :=
  false_finish basis domain capacity radius word (ExtensionQuery.coefficientsQuery basis point) messages _ expected
    (ExtensionQuery.coefficients_evaluate basis point _) accepted wrong

theorem scalar_false_finish (basis : Module.Basis (Fin d) F K)
    (domain : Position ↪ F) (capacity : 2 ^ suffix ≤ m * (d + padding)) (radius : ℕ)
    (word : Position → (Fin (2 ^ front) × Fin (d + padding)) → Fin (d + padding) → F)
    (weights : Fin (d + padding) → K) (point : Fin (front + suffix) → K)
    (messages : Fin (d + padding) → Fin (2 ^ suffix) → F) (expected : K)
    (accepted : PaddedExtension.element basis
      ((ExtensionQuery.scalarQuery basis weights _ point).finish
        (MatrixResponse.finishMessage
          (SubclaimSourceLayout.rightWeights (ExtensionQuery.scalarQuery basis weights _ point).query) messages)) = some expected)
    (wrong : expected ≠ ExtensionQuery.evaluate (front + suffix) point
      (fun cell => ExtensionQuery.laneValue weights (SubclaimSourceLayout.decodedSource domain capacity radius word cell))) :
    MatrixResponse.finishMessage (SubclaimSourceLayout.rightWeights (ExtensionQuery.scalarQuery basis weights _ point).query) messages ≠
      matrixEvaluation (SubclaimSourceLayout.leftWeights (ExtensionQuery.scalarQuery basis weights _ point).query)
        (SubclaimSourceLayout.rightWeights (ExtensionQuery.scalarQuery basis weights _ point).query)
        (MatrixOpeningSecurity.extract domain capacity radius word) :=
  false_finish basis domain capacity radius word (ExtensionQuery.scalarQuery basis weights _ point) messages _ expected
    (ExtensionQuery.scalar_evaluate basis weights point _) accepted wrong

end

end FormalProof4FHE.HasteBoots.ExtensionSourceOpening
