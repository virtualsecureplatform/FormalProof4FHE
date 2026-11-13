module
public import FormalProof4FHE.HasteBoots.DecodedAccumulatorRows
@[expose] public section

/-! Decode full native accumulator constraints without assuming a separately
provided trace or truthful decomposition inputs. -/
namespace FormalProof4FHE.HasteBoots.DecodedAccumulatorConstraints
noncomputable section
variable {q cells lanes rows : ℕ} [Fact q.Prime]

omit [Fact q.Prime] in
/-- A copied half repeats the selected difference in both output halves. -/
theorem decode_copyHalf
    (source : AccumulatorMatrixSoundness.Table (ZMod q) (2^lanes) cells rows)
    (position : Fin (2^rows)) (selected outputHalf : Bool) :
    DecodedAccumulatorRows.decode (AccumulatorMatrixSoundness.copyHalf source selected) position outputHalf =
      DecodedAccumulatorRows.decode source position selected := by
  funext index
  exact congrFun (AccumulatorMatrixSoundness.copyHalf_coordinate source selected outputHalf
    ((PackedAccumulatorTrace.polynomial cells lanes).symm index).1
    ((FlatMatrixFold.index rows).symm position))
    ((PackedAccumulatorTrace.polynomial cells lanes).symm index).2

/-- The actual duplicated source selected by the reconstruction half. -/
def duplicate (sources : AccumulatorMatrixSoundness.Sources (ZMod q) (2^lanes) cells rows)
    (half : Bool) := if half then sources.duplicateB else sources.duplicateA

/-- The two existing residuals enforce full-table duplication. -/
theorem duplicate_of_holds
    (sources : AccumulatorMatrixSoundness.Sources (ZMod q) (2^lanes) cells rows)
    (holds : AccumulatorMatrixSoundness.Holds sources) (half : Bool) :
    duplicate sources half = AccumulatorMatrixSoundness.copyHalf sources.difference half := by
  cases half
  · exact (sub_eq_zero.mp (holds (2 : Fin 5))).symm
  · exact (sub_eq_zero.mp (holds (3 : Fin 5))).symm

/-- Every original duplicated row equals the selected difference polynomial;
this includes padded rows and either physical output half. -/
theorem duplicate_rows_of_holds
    (sources : AccumulatorMatrixSoundness.Sources (ZMod q) (2^lanes) cells rows)
    (holds : AccumulatorMatrixSoundness.Holds sources)
    (position : Fin (2^rows)) (selected outputHalf : Bool) :
    DecodedAccumulatorRows.decode (duplicate sources selected) position outputHalf =
      DecodedAccumulatorRows.decode sources.difference position selected := by
  rw [duplicate_of_holds sources holds selected]
  exact decode_copyHalf sources.difference position selected outputHalf

/-- Decode the existing subtraction and addition residuals into one actual
coefficient trace, with no packed-trace witness supplied by the caller. -/
theorem arithmetic_of_holds
    (sources : AccumulatorMatrixSoundness.Sources (ZMod q) (2^lanes) cells rows)
    (holds : AccumulatorMatrixSoundness.Holds sources) :
    AccumulatorTrace.Arithmetic (DecodedAccumulatorRows.tables sources) := by
  have subtraction := sub_eq_zero.mp (holds (0 : Fin 5))
  have addition := sub_eq_zero.mp (holds (1 : Fin 5))
  constructor
  · intro position
    funext half index
    exact congrFun (congrFun subtraction
      (AccumulatorPackedQueries.coordinate ((PackedAccumulatorTrace.polynomial cells lanes).symm index).1
        ((FlatMatrixFold.index rows).symm position) half))
      ((PackedAccumulatorTrace.polynomial cells lanes).symm index).2
  · intro position
    funext half index
    exact congrFun (congrFun addition
      (AccumulatorPackedQueries.coordinate ((PackedAccumulatorTrace.polynomial cells lanes).symm index).1
        ((FlatMatrixFold.index rows).symm position) half))
      ((PackedAccumulatorTrace.polynomial cells lanes).symm index).2

end
end FormalProof4FHE.HasteBoots.DecodedAccumulatorConstraints
