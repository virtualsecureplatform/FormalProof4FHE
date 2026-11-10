module
public import FormalProof4FHE.HasteBoots.MatrixQueryProjection
public import FormalProof4FHE.HasteBoots.AccumulatorMatrixSoundness
@[expose] public section

/-! Endpoint residuals use the coefficient/half projection of the same common
fresh query. Together with the five full-dimension residuals they cover all
seven arithmetic equations, on fixed sources with truthful evaluations. Native
authentication, checked configuration and Fiat--Shamir refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.AccumulatorEndpointSoundness
open OracleSpec OracleComp Matrix
open PackedSumcheckSubclaim (Query)
open AccumulatorMatrixSoundness (Sources Table)
noncomputable section
variable {F : Type} [Field F] {k c r : ℕ}

abbrev ShortTable (F : Type) (k c : ℕ) := MatrixFold.Cube (1+c) → Fin k → F

def slice (input : Table F k c r) (target : MatrixFold.Cube r) (position : MatrixFold.Cube (1+c)) : Fin k → F :=
  let p := AccumulatorQuerySplit.cubeSplit c 1 position
  input (AccumulatorPackedQueries.coordinate p.1 target p.2.1)

def publicTable (endpoint : Bool → MatrixFold.Cube c → Fin k → F) (position : MatrixFold.Cube (1+c)) : Fin k → F :=
  let p := AccumulatorQuerySplit.cubeSplit c 1 position
  endpoint p.2.1 p.1

omit [Field F] in
theorem slice_append (input : Table F k c r) (target : MatrixFold.Cube r) (cell : MatrixFold.Cube c) (half : Bool) :
    slice input target (MonomialBitOrder.append cell (show MatrixFold.Cube 1 from (half,()))) =
      input (AccumulatorPackedQueries.coordinate cell target half) := by
  unfold slice
  rw [AccumulatorQuerySplit.cubeSplit_append]

omit [Field F] in
theorem publicTable_append (endpoint : Bool → MatrixFold.Cube c → Fin k → F) (cell : MatrixFold.Cube c) (half : Bool) :
    publicTable endpoint (MonomialBitOrder.append cell (show MatrixFold.Cube 1 from (half,()))) = endpoint half cell := by
  unfold publicTable
  rw [AccumulatorQuerySplit.cubeSplit_append]

def rowQuery (query : Query F k ((1+r)+c)) (target : MatrixFold.Cube r) : Query F k ((1+r)+c) :=
  let p := AccumulatorQuerySplit.parts query
  AccumulatorPackedQueries.whole p.1 (AccumulatorShiftQueries.selected target) p.2.2

def expected (query : Query F k ((1+r)+c)) (endpoint : Bool → MatrixFold.Cube c → Fin k → F) : Fin k → F :=
  let p := AccumulatorQuerySplit.parts query
  AccumulatorPackedQueries.correction p.1 p.2.2 1 endpoint

theorem projected_fold (query : Query F k ((1+r)+c)) (table : ShortTable F k c) :
    (MatrixQueryProjection.endpoint query).fold table =
      (AccumulatorQuerySplit.parts query).2.2 false *ᵥ
        (AccumulatorQuerySplit.parts query).1.fold (fun cell => table (MonomialBitOrder.append cell (show MatrixFold.Cube 1 from (false,())))) +
      (AccumulatorQuerySplit.parts query).2.2 true *ᵥ
        (AccumulatorQuerySplit.parts query).1.fold (fun cell => table (MonomialBitOrder.append cell (show MatrixFold.Cube 1 from (true,())))) := by
  rw [MatrixQueryProjection.endpoint_parts]
  exact AccumulatorPackedQueries.whole_fold (AccumulatorQuerySplit.parts query).1 (.nil : Query F k 0)
    (AccumulatorQuerySplit.parts query).2.2 table

theorem fold_slice (query : Query F k ((1+r)+c)) (input : Table F k c r) (target : MatrixFold.Cube r) :
    (MatrixQueryProjection.endpoint query).fold (slice input target) = (rowQuery query target).fold input := by
  rw [projected_fold]
  simp only [slice_append]
  exact (AccumulatorPackedQueries.selectWhole_fold (AccumulatorQuerySplit.parts query).1 target
    (AccumulatorQuerySplit.parts query).2.2 input).symm

theorem fold_public (query : Query F k ((1+r)+c)) (endpoint : Bool → MatrixFold.Cube c → Fin k → F) :
    (MatrixQueryProjection.endpoint query).fold (publicTable endpoint) = expected query endpoint := by
  rw [projected_fold]
  simp only [publicTable_append, expected, AccumulatorPackedQueries.correction, Matrix.one_mulVec]

/-- Fixed coefficient/half source errors at row zero and the last active row. -/
def residual (sources : Sources F k c r) (last : Bool) : ShortTable F k c :=
  if last then slice sources.output sources.finish-publicTable sources.final
  else slice sources.input (AccumulatorShiftQueries.zero r)-publicTable sources.initial

def Holds (sources : Sources F k c r) : Prop := ∀ last, residual sources last = 0

def Check (sources : Sources F k c r) (query : Query F k ((1+r)+c)) : Prop :=
  (rowQuery query (AccumulatorShiftQueries.zero r)).fold sources.input = expected query sources.initial ∧
  (rowQuery query sources.finish).fold sources.output = expected query sources.final

def error (sources : Sources F k c r) (query : Query F k ((1+r)+c)) (last : Bool) : Fin k → F :=
  if last then (rowQuery query sources.finish).fold sources.output-expected query sources.final
  else (rowQuery query (AccumulatorShiftQueries.zero r)).fold sources.input-expected query sources.initial

theorem fold_residual (sources : Sources F k c r) (query : Query F k ((1+r)+c)) (last : Bool) :
    (MatrixQueryProjection.endpoint query).fold (residual sources last) = error sources query last := by
  cases last
  · exact (AccumulatorPackedQueries.fold_sub (MatrixQueryProjection.endpoint query)
      (slice sources.input (AccumulatorShiftQueries.zero r)) (publicTable sources.initial)).trans
      (congrArg₂ (fun (x y : Fin k → F) => x-y) (fold_slice query sources.input _) (fold_public query sources.initial))
  · exact (AccumulatorPackedQueries.fold_sub (MatrixQueryProjection.endpoint query)
      (slice sources.output sources.finish) (publicTable sources.final)).trans
      (congrArg₂ (fun (x y : Fin k → F) => x-y) (fold_slice query sources.output _) (fold_public query sources.final))

theorem check_iff (sources : Sources F k c r) (query : Query F k ((1+r)+c)) :
    Check sources query ↔ ∀ last, (MatrixQueryProjection.endpoint query).fold (residual sources last) = 0 := by
  constructor
  · intro checked last
    cases last
    · exact (fold_residual sources query false).trans (sub_eq_zero.mpr checked.1)
    · exact (fold_residual sources query true).trans (sub_eq_zero.mpr checked.2)
  · intro folded
    exact ⟨sub_eq_zero.mp ((fold_residual sources query false).symm.trans (folded false)),
      sub_eq_zero.mp ((fold_residual sources query true).symm.trans (folded true))⟩

theorem honest_check (sources : Sources F k c r) (holds : Holds sources) (query : Query F k ((1+r)+c)) :
    Check sources query := by
  apply (check_iff sources query).mpr
  intro last
  exact (congrArg (MatrixQueryProjection.endpoint query).fold (holds last)).trans
    (AccumulatorPackedQueries.fold_zero _)

def FullHolds (sources : Sources F k c r) : Prop := AccumulatorMatrixSoundness.Holds sources ∧ Holds sources
def FullCheck (sources : Sources F k c r) (query : Query F k ((1+r)+c)) : Prop :=
  AccumulatorMatrixSoundness.CoreCheck sources query ∧ Check sources query

variable [Fintype F] [DecidableEq F] [SampleableType (Fin k → F)]

theorem fresh_endpoint_bound (nodes : PackedSumcheckRound.Node k ↪ F) (sources : Sources F k c r)
    (falseClaim : ¬Holds sources) :
    Pr{let query ← MatrixCompression.sample nodes ((1+r)+c)}[Check sources query] ≤
      ((1+c : ℕ) : ENNReal) * (((((2*k-1 : ℕ) : ENNReal)/Fintype.card F)^k)) := by
  classical
  change ¬∀ last, residual sources last = 0 at falseClaim
  obtain ⟨last,nonzero⟩ := not_forall.mp falseClaim
  have projected := (MatrixQueryProjection.sample_endpoint nodes c r).prEvent_eq
    (fun query => query.fold (residual sources last) = 0)
  have bound := MatrixCompression.zero_bound nodes (1+c) (residual sources last) nonzero
  have mono := prEvent_mono (MatrixCompression.sample nodes ((1+r)+c)) _ _
    (fun query checked => (check_iff sources query).mp checked last)
  have probability : Pr{let query ← MatrixCompression.sample nodes ((1+r)+c)}[
      (MatrixQueryProjection.endpoint query).fold (residual sources last) = 0] =
      Pr{let query ← MatrixCompression.sample nodes (1+c)}[query.fold (residual sources last) = 0] := by
    simpa only [prEvent_map] using projected
  exact mono.trans (probability.le.trans bound)

/-- All seven fixed arithmetic constraints share one complete query. A false
constraint is selected before sampling, so neither family size nor the two
endpoint checks multiply the full-dimension compression bound. -/
theorem fresh_full_bound (nodes : PackedSumcheckRound.Node k ↪ F) (sources : Sources F k c r)
    (falseClaim : ¬FullHolds sources) :
    Pr{let query ← MatrixCompression.sample nodes ((1+r)+c)}[FullCheck sources query] ≤
      ((((1+r)+c : ℕ) : ENNReal) * (((((2*k-1 : ℕ) : ENNReal)/Fintype.card F)^k))) := by
  classical
  by_cases core : AccumulatorMatrixSoundness.Holds sources
  · have endpoints : ¬Holds sources := fun good => falseClaim ⟨core,good⟩
    exact (prEvent_mono _ _ _ (fun _ checked => checked.2)).trans
      ((fresh_endpoint_bound nodes sources endpoints).trans
        (by gcongr; exact_mod_cast (show 1 ≤ 1+r by omega)))
  · exact (prEvent_mono _ _ _ (fun _ checked => checked.1)).trans
      (AccumulatorMatrixSoundness.fresh_core_bound nodes sources core)

end
end FormalProof4FHE.HasteBoots.AccumulatorEndpointSoundness
