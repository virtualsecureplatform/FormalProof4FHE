module

public import FormalProof4FHE.HasteBoots.ProximityOpening
public import FormalProof4FHE.HasteBoots.StructuredOpening

@[expose] public section

/-!
# Native full-width test responses and the analysis field

The verifier tests each base-field lane and each coordinate of the same block.
These equalities imply the scalar equality used in the row-span argument.
The symbol-field response is derived from native responses, not supplied by
the prover as an extra protocol message.
-/

open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.ResponseAssembly

noncomputable section

variable {F K Row Position : Type} [Field F] [Field K] [Algebra F K] {b m : ℕ}

/-- Assemble the full-width family of base-field response lanes. -/
def assemble (basis : Module.Basis (Fin b) F K)
    (responses : Fin b → Position → Fin b → F) : Position → K :=
  fun pos => ∑ lane, basis lane * SymbolLift.pack basis (responses lane pos)

/-- Packing commutes with every base-linear row combination. -/
theorem pack_combine [Fintype Row] (basis : Module.Basis (Fin b) F K)
    (weights : Row → F) (word : Position → Row → Fin b → F) (pos : Position) :
    SymbolLift.pack basis (StructuredOpening.combine weights word pos) =
      ∑ row, algebraMap F K (weights row) * SymbolLift.pack basis (word pos row) := by
  classical
  unfold StructuredOpening.combine
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [(SymbolLift.pack basis).map_smul]
  exact Algebra.smul_def _ _

/-- The analysis linear combination is exactly the assembly of the native test lanes. -/
theorem randomWord_eq_assemble [Fintype Row] (basis : Module.Basis (Fin b) F K)
    (word : Position → Row → Fin b → F) (matrix : Fin b → Row → F) :
    ProximityOpening.randomWord basis word matrix =
      assemble basis (fun lane => StructuredOpening.combine (matrix lane) word) := by
  classical
  funext pos
  simp only [ProximityOpening.randomWord, Fintype.linearCombination_apply,
    RowSpanSampling.rowFamily, BaseMatrixProximity.stack, Matrix.of_symm_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply, assemble, pack_combine]
  exact (SymbolLift.combine_tests basis matrix (fun row => SymbolLift.pack basis (word pos row))).symm

/-- Encoded base-field response lanes assemble to a scalar RS codeword. -/
theorem assemble_encoded_mem (basis : Module.Basis (Fin b) F K) (domain : Position ↪ F)
    (responses : Fin b → Fin m → Fin b → F) :
    assemble basis (fun lane => BlockEncoder.encode domain (responses lane)) ∈
      ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m := by
  classical
  have equal : assemble basis (fun lane => BlockEncoder.encode domain (responses lane)) =
      ∑ lane, basis lane • SymbolLift.packWord basis (BlockEncoder.encode domain (responses lane)) := by
    ext pos
    simp only [assemble, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, SymbolLift.packWord]
  rw [equal]
  apply Submodule.sum_mem
  intro lane _
  exact Submodule.smul_mem _ _ (SymbolLift.encode_mem_scalarCode basis domain (responses lane))

/-- Every native lane passing on the same columns implies the scalar check there. -/
theorem agrees_of_lanes [Fintype Row] (basis : Module.Basis (Fin b) F K)
    (word : Position → Row → Fin b → F) (matrix : Fin b → Row → F)
    (responses : Fin b → Position → Fin b → F) {queries : ℕ}
    (draw : Fin queries → Position)
    (checked : ∀ lane, ColumnOpening.Agrees (StructuredOpening.combine (matrix lane) word)
      (responses lane) draw) :
    ColumnOpening.Agrees (ProximityOpening.randomWord basis word matrix)
      (assemble basis responses) draw := by
  intro i
  rw [randomWord_eq_assemble]
  unfold assemble
  apply Finset.sum_congr rfl
  intro lane _
  exact congrArg (fun symbol => basis lane * SymbolLift.pack basis symbol) (checked lane i)

end

end FormalProof4FHE.HasteBoots.ResponseAssembly
