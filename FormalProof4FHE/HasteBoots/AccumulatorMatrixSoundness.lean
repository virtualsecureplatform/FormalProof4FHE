module
public import FormalProof4FHE.HasteBoots.AccumulatorQuerySplit
public import FormalProof4FHE.HasteBoots.MatrixCompression
@[expose] public section

/-! Fixed-source residuals and fresh-query detection for the accumulator's
five full-dimension equations. Endpoint-selection checks, authentication and
production Fiat--Shamir refinement are separate obligations. -/
namespace FormalProof4FHE.HasteBoots.AccumulatorMatrixSoundness
open scoped BigOperators
open OracleSpec OracleComp Matrix
open PackedSumcheckSubclaim (Query)
noncomputable section

abbrev Table (F : Type) (k c r : ℕ) := MatrixFold.Cube ((1+r)+c) → Fin k → F

structure Sources (F : Type) (k c r : ℕ) where
  input : Table F k c r
  product : Table F k c r
  difference : Table F k c r
  external : Table F k c r
  output : Table F k c r
  duplicateA : Table F k c r
  duplicateB : Table F k c r
  initial : Bool → MatrixFold.Cube c → Fin k → F
  final : Bool → MatrixFold.Cube c → Fin k → F
  start : MatrixFold.Cube r
  finish : MatrixFold.Cube r

variable {F : Type} [Field F] {k c r : ℕ}

def copyHalf (input : Table F k c r) (half : Bool) (position : MatrixFold.Cube ((1+r)+c)) : Fin k → F :=
  let p := AccumulatorQuerySplit.coordinates c r position
  input (AccumulatorPackedQueries.coordinate p.1 p.2.1 half)

def advance (input : Table F k c r) (position : MatrixFold.Cube ((1+r)+c)) : Fin k → F :=
  let p := AccumulatorQuerySplit.coordinates c r position
  input (AccumulatorPackedQueries.coordinate p.1 (AccumulatorShiftQueries.successor p.2.1) p.2.2)

def boundary (target : MatrixFold.Cube r) (endpoint : Bool → MatrixFold.Cube c → Fin k → F)
    (position : MatrixFold.Cube ((1+r)+c)) : Fin k → F :=
  let p := AccumulatorQuerySplit.coordinates c r position
  AccumulatorPackedQueries.impulse target (endpoint p.2.2 p.1) p.2.1

omit [Field F] in
theorem copyHalf_coordinate (input : Table F k c r) (target choice : Bool)
    (cell : MatrixFold.Cube c) (row : MatrixFold.Cube r) :
    copyHalf input target (AccumulatorPackedQueries.coordinate cell row choice) =
      input (AccumulatorPackedQueries.coordinate cell row target) := by
  simp only [copyHalf, AccumulatorQuerySplit.coordinates_apply]

omit [Field F] in
theorem advance_coordinate (input : Table F k c r) (choice : Bool)
    (cell : MatrixFold.Cube c) (row : MatrixFold.Cube r) :
    advance input (AccumulatorPackedQueries.coordinate cell row choice) =
      input (AccumulatorPackedQueries.coordinate cell (AccumulatorShiftQueries.successor row) choice) := by
  simp only [advance, AccumulatorQuerySplit.coordinates_apply]

theorem boundary_coordinate (target : MatrixFold.Cube r) (endpoint : Bool → MatrixFold.Cube c → Fin k → F)
    (choice : Bool) (cell : MatrixFold.Cube c) (row : MatrixFold.Cube r) :
    boundary target endpoint (AccumulatorPackedQueries.coordinate cell row choice) =
      AccumulatorPackedQueries.impulse target (endpoint choice cell) row := by
  simp only [boundary, AccumulatorQuerySplit.coordinates_apply]

def selectedQuery (query : Query F k ((1+r)+c)) (target : Bool) : Query F k ((1+r)+c) :=
  let p := AccumulatorQuerySplit.parts query
  AccumulatorPackedQueries.whole p.1 p.2.1 (AccumulatorPackedQueries.selectHalf p.2.2 target)

def shiftedQueries (query : Query F k ((1+r)+c)) : List (Query F k ((1+r)+c)) :=
  let p := AccumulatorQuerySplit.parts query
  AccumulatorPackedQueries.shiftWhole p.1 p.2.1 p.2.2

def correction (query : Query F k ((1+r)+c)) (target : MatrixFold.Cube r)
    (endpoint : Bool → MatrixFold.Cube c → Fin k → F) : Fin k → F :=
  let p := AccumulatorQuerySplit.parts query
  AccumulatorPackedQueries.correction p.1 p.2.2 (AccumulatorShiftQueries.weight p.2.1 target) endpoint

theorem fold_copyHalf (query : Query F k ((1+r)+c)) (input : Table F k c r) (target : Bool) :
    query.fold (copyHalf input target) = (selectedQuery query target).fold input := by
  have same := AccumulatorPackedQueries.duplicate_fold (AccumulatorQuerySplit.parts query).1
    (AccumulatorQuerySplit.parts query).2.1 target (AccumulatorQuerySplit.parts query).2.2 input (copyHalf input target)
    (fun cell row choice => copyHalf_coordinate input target choice cell row)
  rw [AccumulatorQuerySplit.rebuild] at same
  exact same.symm

theorem fold_advance (query : Query F k ((1+r)+c)) (input : Table F k c r) :
    query.fold (advance input) = ((shiftedQueries query).map (fun branch => branch.fold input)).sum := by
  have source : (AccumulatorPackedQueries.whole (AccumulatorQuerySplit.parts query).1
      (AccumulatorQuerySplit.parts query).2.1 (AccumulatorQuerySplit.parts query).2.2).fold (advance input) =
      ((shiftedQueries query).map (fun branch => branch.fold input)).sum := by
    rw [AccumulatorPackedQueries.whole_fold]
    simp only [shiftedQueries, AccumulatorPackedQueries.shiftWhole_fold, advance_coordinate]
  rw [AccumulatorQuerySplit.rebuild] at source
  exact source

theorem fold_boundary (query : Query F k ((1+r)+c)) (target : MatrixFold.Cube r)
    (endpoint : Bool → MatrixFold.Cube c → Fin k → F) :
    query.fold (boundary target endpoint) = correction query target endpoint := by
  have same := AccumulatorPackedQueries.whole_impulse (AccumulatorQuerySplit.parts query).1
    (AccumulatorQuerySplit.parts query).2.1 (AccumulatorQuerySplit.parts query).2.2 target endpoint (boundary target endpoint)
    (fun cell row choice => boundary_coordinate target endpoint choice cell row)
  rw [AccumulatorQuerySplit.rebuild] at same
  exact same

/-- Fixed before any query: subtraction, addition, duplicated-a, duplicated-b,
and cyclic continuity with both public boundary corrections. -/
def residual (sources : Sources F k c r) (role : Fin 5) : Table F k c r :=
  if role.val = 0 then sources.difference-(sources.product-sources.input)
  else if role.val = 1 then sources.output-(sources.input+sources.external)
  else if role.val = 2 then copyHalf sources.input false-sources.duplicateA
  else if role.val = 3 then copyHalf sources.input true-sources.duplicateB
  else advance sources.input-sources.output-(boundary sources.start sources.initial-boundary sources.finish sources.final)

def Holds (sources : Sources F k c r) : Prop := ∀ role, residual sources role = 0

/-- Literal truthful-source values of the five full-dimension native equations.
The separately selected initial/final endpoint checks are not included here. -/
def CoreCheck (sources : Sources F k c r) (query : Query F k ((1+r)+c)) : Prop :=
  query.fold sources.difference = query.fold sources.product-query.fold sources.input ∧
  query.fold sources.output = query.fold sources.input+query.fold sources.external ∧
  (selectedQuery query false).fold sources.input = query.fold sources.duplicateA ∧
  (selectedQuery query true).fold sources.input = query.fold sources.duplicateB ∧
  ((shiftedQueries query).map (fun branch => branch.fold sources.input)).sum-query.fold sources.output =
    correction query sources.start sources.initial-correction query sources.finish sources.final

def error (sources : Sources F k c r) (query : Query F k ((1+r)+c)) (role : Fin 5) : Fin k → F :=
  if role.val = 0 then query.fold sources.difference-(query.fold sources.product-query.fold sources.input)
  else if role.val = 1 then query.fold sources.output-(query.fold sources.input+query.fold sources.external)
  else if role.val = 2 then (selectedQuery query false).fold sources.input-query.fold sources.duplicateA
  else if role.val = 3 then (selectedQuery query true).fold sources.input-query.fold sources.duplicateB
  else ((shiftedQueries query).map (fun branch => branch.fold sources.input)).sum-query.fold sources.output-
    (correction query sources.start sources.initial-correction query sources.finish sources.final)

theorem fold_residual (sources : Sources F k c r) (query : Query F k ((1+r)+c)) (role : Fin 5) :
    query.fold (residual sources role) = error sources query role := by
  fin_cases role
  · exact (AccumulatorPackedQueries.fold_sub query sources.difference (sources.product-sources.input)).trans
      (congrArg (query.fold sources.difference-·) (AccumulatorPackedQueries.fold_sub query sources.product sources.input))
  · exact (AccumulatorPackedQueries.fold_sub query sources.output (sources.input+sources.external)).trans
      (congrArg (query.fold sources.output-·) (AccumulatorPackedQueries.fold_add query sources.input sources.external))
  · exact (AccumulatorPackedQueries.fold_sub query (copyHalf sources.input false) sources.duplicateA).trans
      (congrArg (·-query.fold sources.duplicateA) (fold_copyHalf query sources.input false))
  · exact (AccumulatorPackedQueries.fold_sub query (copyHalf sources.input true) sources.duplicateB).trans
      (congrArg (·-query.fold sources.duplicateB) (fold_copyHalf query sources.input true))
  · have first := (AccumulatorPackedQueries.fold_sub query (advance sources.input) sources.output).trans
      (congrArg (·-query.fold sources.output) (fold_advance query sources.input))
    have last := (AccumulatorPackedQueries.fold_sub query (boundary sources.start sources.initial) (boundary sources.finish sources.final)).trans
      (congrArg₂ (fun (x y : Fin k → F) => x-y) (fold_boundary query sources.start sources.initial) (fold_boundary query sources.finish sources.final))
    exact (AccumulatorPackedQueries.fold_sub query (advance sources.input-sources.output)
      (boundary sources.start sources.initial-boundary sources.finish sources.final)).trans
      (congrArg₂ (fun (x y : Fin k → F) => x-y) first last)

theorem error_zero_iff (sources : Sources F k c r) (query : Query F k ((1+r)+c)) :
    (∀ role, error sources query role = 0) ↔ CoreCheck sources query := by
  constructor
  · intro zero
    exact ⟨sub_eq_zero.mp (zero 0),sub_eq_zero.mp (zero 1),sub_eq_zero.mp (zero 2),
      sub_eq_zero.mp (zero 3),sub_eq_zero.mp (zero 4)⟩
  · intro checked role
    fin_cases role
    · exact sub_eq_zero.mpr checked.1
    · exact sub_eq_zero.mpr checked.2.1
    · exact sub_eq_zero.mpr checked.2.2.1
    · exact sub_eq_zero.mpr checked.2.2.2.1
    · exact sub_eq_zero.mpr checked.2.2.2.2

theorem coreCheck_iff (sources : Sources F k c r) (query : Query F k ((1+r)+c)) :
    CoreCheck sources query ↔ ∀ role, query.fold (residual sources role) = 0 := by
  constructor
  · intro checked role
    exact (fold_residual sources query role).trans ((error_zero_iff sources query).mpr checked role)
  · intro folded
    apply (error_zero_iff sources query).mp
    intro role
    exact (fold_residual sources query role).symm.trans (folded role)

theorem honest_coreCheck (sources : Sources F k c r) (holds : Holds sources) (query : Query F k ((1+r)+c)) :
    CoreCheck sources query := by
  apply (coreCheck_iff sources query).mpr
  intro role
  exact (congrArg query.fold (holds role)).trans (AccumulatorPackedQueries.fold_zero query)

variable [Fintype F] [DecidableEq F] [SampleableType (Fin k → F)]

/-- A false fixed full-dimension accumulator constraint family pays one common
fresh-query compression error, without a five-equation or source-count loss.
This is not endpoint-check, authentication or Fiat--Shamir soundness. -/
theorem fresh_core_bound (nodes : PackedSumcheckRound.Node k ↪ F) (sources : Sources F k c r)
    (falseClaim : ¬Holds sources) :
    Pr{let query ← MatrixCompression.sample nodes ((1+r)+c)}[CoreCheck sources query] ≤
      (((1+r)+c : ℕ) : ENNReal) * (((((2*k-1 : ℕ) : ENNReal) / Fintype.card F)^k)) := by
  classical
  change ¬∀ role, residual sources role = 0 at falseClaim
  obtain ⟨role,nonzero⟩ := not_forall.mp falseClaim
  exact (prEvent_mono _ _ _ (fun query checked => (coreCheck_iff sources query).mp checked role)).trans
    (MatrixCompression.zero_bound nodes ((1+r)+c) (residual sources role) nonzero)

end
end FormalProof4FHE.HasteBoots.AccumulatorMatrixSoundness
