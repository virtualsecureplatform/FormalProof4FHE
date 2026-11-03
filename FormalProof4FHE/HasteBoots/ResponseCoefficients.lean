module

public import FormalProof4FHE.HasteBoots.CodeCorrespondence
public import FormalProof4FHE.HasteBoots.StructuredOpening
public import FormalProof4FHE.HasteBoots.RowLayout

@[expose] public section

/-!
# Recovering response coefficients from semantic encoded words

This is a total information-theoretic inverse. Its use is confined to the
analysis finishing map and common-source extractor. It is not asserted to be
an efficient production decoder. When m is at most the domain length, every
encoded response recovers its exact original coefficients.
-/

open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.ResponseCoefficients

noncomputable section

variable {F Position Row : Type} [Field F] {m b size : ℕ}

/-- A total inverse; only its behavior on coded words is used. -/
def decode (domain : Position → F) (word : Position → Fin b → F) : Fin m → Fin b → F :=
  Function.invFun (BlockEncoder.encode domain) word

theorem decode_encode [Fintype Position] (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (coefficients : Fin m → Fin b → F) :
    decode domain (BlockEncoder.encode domain coefficients) = coefficients :=
  Function.leftInverse_invFun (BlockEncoder.encode_injective domain enough) coefficients

theorem encode_decode [Fintype Position] [NeZero m] [NeZero b]
    (domain : Position ↪ F) (word : Position → Fin b → F)
    (coded : word ∈ BlockCode.code domain m b) :
    BlockEncoder.encode domain (decode (m := m) domain word) = word := by
  obtain ⟨coefficients, equal⟩ := CodeCorrespondence.baseRepresentation domain word coded
  rw [← equal]
  exact Function.apply_invFun_apply

/-- Row aggregation in the coefficient representation. -/
def aggregate [Fintype Row] (weights : Row → F) (messages : Row → Fin m → Fin b → F) :
    Fin m → Fin b → F := ∑ row, weights row • messages row

/-- The native zero-padding operation commutes with row aggregation. -/
theorem padded_aggregate [Fintype Row] (weights : Row → F) (messages : Row → Fin size → F) :
    RowLayout.padded (m := m) (b := b) (fun right => ∑ row, weights row * messages row right) =
      aggregate weights (fun row => RowLayout.padded (messages row)) := by
  classical
  funext block lane
  by_cases present : (finProdFinEquiv (block, lane)).val < size
  · simp [RowLayout.padded, aggregate, Finset.sum_apply]
  · simp [RowLayout.padded, aggregate, Finset.sum_apply]

/-- Semantic encoding commutes with the native row aggregation. -/
theorem encode_aggregate [Fintype Row] (domain : Position → F) (weights : Row → F)
    (messages : Row → Fin m → Fin b → F) :
    BlockEncoder.encode domain (aggregate weights messages) =
      StructuredOpening.combine weights (fun pos row => BlockEncoder.encode domain (messages row) pos) := by
  classical
  ext pos lane
  simp only [BlockEncoder.encode, aggregate, StructuredOpening.combine, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_assoc _ _ _

/-- The coefficient inverse is linear on coded rows of one common source. -/
theorem decode_combine [Fintype Position] [Fintype Row] [NeZero m] [NeZero b]
    (domain : Position ↪ F) (enough : m ≤ Fintype.card Position)
    (weights : Row → F) (source : Position → Row → Fin b → F)
    (coded : CommonSource.RowsIn (BlockCode.code domain m b) source) :
    decode (m := m) domain (StructuredOpening.combine weights source) =
      aggregate weights (fun row => decode domain (fun pos => source pos row)) := by
  apply BlockEncoder.encode_injective domain enough
  rw [encode_decode domain _ (StructuredOpening.combine_mem _ weights source coded), encode_aggregate]
  congr 1
  funext pos row
  exact (congrFun (encode_decode domain (fun pos => source pos row) (coded row)) pos).symm

/-- Truncation to the original message length commutes with aggregation, even
when the source coefficients contain nonzero entries in padding positions. -/
theorem recover_aggregate [Fintype Row] (capacity : size ≤ m * b)
    (weights : Row → F) (messages : Row → Fin m → Fin b → F) :
    RowLayout.recover capacity (aggregate weights messages) =
      fun index => ∑ row, weights row * RowLayout.recover capacity (messages row) index := by
  classical
  funext index
  simp only [RowLayout.recover, aggregate, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end

end FormalProof4FHE.HasteBoots.ResponseCoefficients
