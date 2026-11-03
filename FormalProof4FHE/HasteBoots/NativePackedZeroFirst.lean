module

public import FormalProof4FHE.HasteBoots.PackedZeroReduction

@[expose] public section

/-!
# Native special-first-message boundary checker

The typed native first message has k rows of D+1 evaluations. Every one of the
first 2*k entries in every row must be zero. The Boolean nested loop is exactly
the semantic boundary condition on the interpolated polynomial family. Raw
vector-length rejection and Rust/byte decoding are separate refinement tasks.
-/

namespace FormalProof4FHE.HasteBoots.NativePackedZeroFirst

noncomputable section

variable {F : Type} [Field F] {k degree : ℕ}

theorem nodeIndex_surjective : Function.Surjective (NativePackedInterpolation.nodeIndex (k := k)) := by
  apply ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨NativePackedInterpolation.nodeIndex_injective, ?_⟩).2
  simp only [PackedSumcheckRound.Node, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]

def checkFirst [DecidableEq F] (enough : 2 * k ≤ degree + 1)
    (message : Fin k → Fin (degree + 1) → F) : Bool :=
  (List.ofFn fun point : Fin k =>
    (List.ofFn fun index : Fin (2 * k) => decide (message point (Fin.castLE enough index) = 0)).all id).all id

theorem checkFirst_iff [DecidableEq F] (enough : 2 * k ≤ degree + 1)
    (message : Fin k → Fin (degree + 1) → F) :
    checkFirst enough message = true ↔ ∀ point index, message point (Fin.castLE enough index) = 0 := by
  simp [checkFirst, List.mem_ofFn, List.all_eq_true]

/-- Interleaved Boolean/lane nodes cover all native boundary entries, without
requiring a positive width or any distinct sampled equality points. -/
theorem checkFirst_boundary_iff [DecidableEq F] (p : ℕ) [CharP F p]
    (small : degree + 1 ≤ p) (enough : 2 * k ≤ degree + 1)
    (message : Fin k → Fin (degree + 1) → F) :
    checkFirst enough message = true ↔
      PackedZeroFirst.Boundary (NativePackedInterpolation.nodes p (enough.trans small))
        (fun point => NativePackedInterpolation.messagePolynomial
          (NativePackedInterpolation.consecutive p small) (message point)) := by
  have evalAt (point : Fin k) (node : PackedSumcheckRound.Node k) :
      (NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive p small) (message point)).eval
        (NativePackedInterpolation.nodes p (enough.trans small) node) =
          message point (Fin.castLE enough (NativePackedInterpolation.nodeIndex node)) :=
    NativePackedInterpolation.messagePolynomial_node (NativePackedInterpolation.consecutive p small)
      (message point) (Fin.castLE enough (NativePackedInterpolation.nodeIndex node))
  rw [checkFirst_iff]
  simp only [PackedZeroFirst.Boundary, evalAt]
  constructor
  · intro allEntries point bit lane
    exact allEntries point _
  · intro boundary point index
    obtain ⟨⟨bit, lane⟩, equal⟩ := nodeIndex_surjective index
    rw [← equal]
    exact boundary point bit lane

end

end FormalProof4FHE.HasteBoots.NativePackedZeroFirst
