module
public import FormalProof4FHE.HasteBoots.PCSParameters
public import FormalProof4FHE.HasteBoots.RectangularOpeningKernel
@[expose] public section

/-! Exact arithmetic for independent base-field test rows. The entire quotient
is raised to the test width. Code-symbol width affects distance/geometry,
not the exponent or the alphabet cardinality. -/
namespace FormalProof4FHE.HasteBoots.RectangularPCSParameters
open PCSParameters (distance miss)
noncomputable section

def proximity (prime tests height message : ℕ) : ENNReal :=
  ((distance height message : ENNReal)/(prime : ENNReal))^tests

def columns (height message queries radius : ℕ) : ENNReal :=
  max (miss height queries (distance height message-radius)) (miss height queries (radius+1))

def error (prime tests height message queries radius : ℕ) : ENNReal :=
  proximity prime tests height message + columns height message queries radius

def finiteProximity (prime tests height message : ℕ) : NNReal :=
  ((distance height message : NNReal)/(prime : NNReal))^tests

def finiteColumns (height message queries radius : ℕ) : NNReal :=
  max ((((2^height-(distance height message-radius) : ℕ) : NNReal)/(2^height : ℕ))^queries)
    ((((2^height-(radius+1) : ℕ) : NNReal)/(2^height : ℕ))^queries)

def finiteError (prime tests height message queries radius : ℕ) : NNReal :=
  finiteProximity prime tests height message + finiteColumns height message queries radius

theorem finiteProximity_coe (prime tests height message : ℕ) (nonzero : prime ≠ 0) :
    (finiteProximity prime tests height message : ENNReal) = proximity prime tests height message := by
  have positive : (prime : NNReal) ≠ 0 := Nat.cast_ne_zero.mpr nonzero
  simp only [finiteProximity,proximity,ENNReal.coe_pow,ENNReal.coe_div positive,ENNReal.coe_natCast]

theorem finiteColumns_coe (height message queries radius : ℕ) :
    (finiteColumns height message queries radius : ENNReal) = columns height message queries radius := by
  have positive : ((2^height : ℕ) : NNReal) ≠ 0 := by positivity
  simp only [finiteColumns,columns,miss,ENNReal.coe_max,ENNReal.coe_pow,ENNReal.coe_div positive,ENNReal.coe_natCast]

theorem finiteError_coe (prime tests height message queries radius : ℕ) (nonzero : prime ≠ 0) :
    (finiteError prime tests height message queries radius : ENNReal) = error prime tests height message queries radius := by
  rw [finiteError,ENNReal.coe_add,finiteProximity_coe _ _ _ _ nonzero,finiteColumns_coe,error]

variable {F : Type} [Field F] [DecidableEq F] [Fintype F]

theorem proximity_eq (height message codeWidth tests : ℕ) [NeZero codeWidth]
    (domain : Fin (2^height) ↪ F) (positive : 0 < message) :
    ((Code.minDist (BlockCode.code domain message codeWidth : Set (Fin (2^height) → Fin codeWidth → F)) : ENNReal)/Fintype.card F)^tests =
      proximity (Fintype.card F) tests height message := by
  rw [BlockCode.minDist domain message codeWidth positive,Fintype.card_fin]
  rfl

omit [Fintype F] in
theorem columns_eq (height message codeWidth queries radius : ℕ) [NeZero codeWidth]
    (domain : Fin (2^height) ↪ F) (positive : 0 < message) :
    max (ColumnOpening.missBound (Fin (2^height)) queries
      (Code.minDist (BlockCode.code domain message codeWidth : Set (Fin (2^height) → Fin codeWidth → F))-radius))
      (ColumnOpening.missBound (Fin (2^height)) queries (radius+1)) = columns height message queries radius := by
  rw [BlockCode.minDist domain message codeWidth positive,Fintype.card_fin]
  simp only [ColumnOpening.missBound,Fintype.card_fin,columns,miss,distance]
end
end FormalProof4FHE.HasteBoots.RectangularPCSParameters
