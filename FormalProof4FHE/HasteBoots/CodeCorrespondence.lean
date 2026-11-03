module

public import FormalProof4FHE.HasteBoots.SymbolLift
public import FormalProof4FHE.HasteBoots.CommonSource
public import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section

/-!
# Exact correspondence of the block code and the symbol-field code

Membership is preserved in BOTH directions, not just for honest codewords.
The degree bound is positive, as it is in validated native row layouts.
This prevents a field-code nearby word from introducing an unmodeled decoder
outside the base-field coordinate code.
-/

open scoped BigOperators
open Module

namespace FormalProof4FHE.HasteBoots.CodeCorrespondence

variable {F K Position : Type} [Field F] [Field K] [Algebra F K] {m b : ℕ}

/-- Every scalar RS word has exactly the bounded-coefficient evaluation representation. -/
theorem scalarRepresentation {R : Type} [Field R] (domain : Position ↪ R)
    [NeZero m] (word : Position → R) (member : word ∈ ReedSolomon.code domain m) :
    ∃ coefficients : Fin m → R, ∀ pos,
      word pos = ∑ j : Fin m, coefficients j * domain pos ^ j.val := by
  obtain ⟨p, degree, values⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp member
  refine ⟨fun j => p.coeff j.val, ?_⟩
  intro pos
  rw [← values pos]
  simpa [Finset.sum_range] using Polynomial.eval_eq_sum_range' degree (domain pos)

/-- Every base block-code word is a coordinate-wise encoding, not just an abstract member. -/
theorem baseRepresentation [Fintype Position] [NeZero m] [NeZero b]
    (domain : Position ↪ F) (word : Position → Fin b → F)
    (member : word ∈ BlockCode.code domain m b) :
    ∃ input : Fin m → Fin b → F, BlockEncoder.encode domain input = word := by
  classical
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  change ∀ lane, (fun pos => word pos lane) ∈ ReedSolomon.code domain ((b * m) / b) at member
  rw [Nat.mul_div_right _ hb] at member
  have repr := fun lane => scalarRepresentation domain (fun pos => word pos lane) (member lane)
  choose coefficients values using repr
  refine ⟨fun j lane => coefficients lane j, ?_⟩
  funext pos lane
  exact (values lane pos).symm

/-- Every symbol-field RS word is the packing of a base-coordinate encoding. -/
theorem scalarRepresentation_base [NeZero m] (basis : Basis (Fin b) F K)
    (domain : Position ↪ F) (word : Position → K)
    (member : word ∈ ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m) :
    ∃ input : Fin m → Fin b → F,
      SymbolLift.packWord basis (BlockEncoder.encode domain input) = word := by
  classical
  obtain ⟨coefficients, values⟩ := scalarRepresentation _ word member
  refine ⟨fun j => basis.equivFun (coefficients j), ?_⟩
  funext pos
  rw [SymbolLift.pack_encode, values pos]
  simp [SymbolLift.pack, SymbolLift.liftedDomain]

/-- Exact code equivalence is essential to transfer the out-of-promise event. -/
theorem mem_code_iff [Fintype Position] [NeZero m] [NeZero b]
    (basis : Basis (Fin b) F K) (domain : Position ↪ F) (word : Position → Fin b → F) :
    word ∈ BlockCode.code domain m b ↔
      SymbolLift.packWord basis word ∈
        ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m := by
  constructor
  · intro member
    obtain ⟨input, rfl⟩ := baseRepresentation domain word member
    exact SymbolLift.encode_mem_scalarCode basis domain input
  · intro member
    obtain ⟨input, h⟩ := scalarRepresentation_base basis domain _ member
    have equalWord : BlockEncoder.encode domain input = word := by
      funext pos
      exact (SymbolLift.pack basis).injective (congrFun h pos)
    rw [← equalWord]
    exact BlockEncoder.encode_mem_code domain input

noncomputable section

/-- Assemble each row symbol without changing the shared column index. -/
def packMatrix {Row : Type} (basis : Basis (Fin b) F K)
    (word : Position → Row → Fin b → F) : Position → Row → K :=
  fun pos row => SymbolLift.pack basis (word pos row)

/-- Packing preserves disagreement of entire columns, including all rows at once. -/
theorem matrix_distance_eq {Row : Type} [Fintype Position]
    [DecidableEq F] [DecidableEq K] [DecidableEq (Row → Fin b → F)]
    [DecidableEq (Row → K)] (basis : Basis (Fin b) F K)
    (left right : Position → Row → Fin b → F) :
    hammingDist (packMatrix basis left) (packMatrix basis right) =
      hammingDist left right := by
  apply hammingDist_comp (x := left) (y := right)
    (fun _ (column : Row → Fin b → F) row => SymbolLift.pack basis (column row))
  intro pos left right equal
  funext row
  exact (SymbolLift.pack basis).injective (congrFun equal row)

/-- A nearby common coded source exists over the base coordinates iff one exists
over the symbol field. The radius counts whole shared columns in both cases. -/
theorem nearby_iff {Row : Type} [Fintype Position] [NeZero m] [NeZero b]
    [DecidableEq F] [DecidableEq K] [DecidableEq (Row → Fin b → F)]
    [DecidableEq (Row → K)] (basis : Basis (Fin b) F K)
    (domain : Position ↪ F) (radius : ℕ) (word : Position → Row → Fin b → F) :
    (∃ source, CommonSource.RowsIn (BlockCode.code domain m b) source ∧
      hammingDist word source ≤ radius) ↔
    (∃ source, CommonSource.RowsIn
      (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m) source ∧
      hammingDist (packMatrix basis word) source ≤ radius) := by
  constructor
  · rintro ⟨source, coded, close⟩
    refine ⟨packMatrix basis source, fun row =>
      (mem_code_iff basis domain _).mp (coded row), ?_⟩
    rwa [matrix_distance_eq]
  · rintro ⟨source, coded, close⟩
    let base : Position → Row → Fin b → F := fun pos row => basis.equivFun (source pos row)
    have packed : packMatrix basis base = source := by
      funext pos row
      exact basis.equivFun.symm_apply_apply _
    refine ⟨base, ?_, ?_⟩
    · intro row
      apply (mem_code_iff basis domain _).mpr
      change (fun pos => packMatrix basis base pos row) ∈ _
      rw [packed]
      exact coded row
    · rw [← packed, matrix_distance_eq] at close
      exact close

end

end FormalProof4FHE.HasteBoots.CodeCorrespondence
