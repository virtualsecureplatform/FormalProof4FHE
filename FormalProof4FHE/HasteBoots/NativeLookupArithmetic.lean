module

public import FormalProof4FHE.HasteBoots.NativeLookupHelper
public import FormalProof4FHE.HasteBoots.LookupPairArithmetic

@[expose] public section

/-!
# Native lookup compression and table sums meet the soundness arithmetic

The native literal zip/fold is retained for all list inputs. For trusted
rectangular public tables it is exactly the tuple hash used by the existing
lookup soundness analysis. Both native reciprocal policies supply its same
public multiplicity sum in the field. This is an arithmetic bridge, not a
claim about raw serialized representatives or the whole verifier.
-/

namespace FormalProof4FHE.HasteBoots.NativeLookupArithmetic

noncomputable section

variable {p width size : ℕ} [Fact (Nat.Prime p)] {K : Type} [Field K] [Algebra (ZMod p) K]

private theorem fold_zip (weights : List K) (row : List (ZMod p)) (initial : K) :
    (row.zip weights).foldl (fun out pair => out + pair.2 * algebraMap (ZMod p) K pair.1) initial =
      (weights.zipWith (fun weight value => weight * algebraMap (ZMod p) K value) row).foldl (fun out value => out + value) initial := by
  induction row generalizing weights initial with
  | nil => cases weights <;> rfl
  | cons value tail ih =>
    cases weights with
    | nil => rfl
    | cons weight rest => exact ih rest (initial + weight * algebraMap (ZMod p) K value)

theorem powersFrom_eq (y start : K) (count : ℕ) :
    NativeLookupChallenge.powersFrom y count start = TupleHash.powers y start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp only [NativeLookupChallenge.powersFrom, TupleHash.powers, ih]

/-- No row reordering, extra coefficient, or changed multiplication order
is hidden in the bridge from the compiled native challenge. -/
theorem compress_tuple (y : K) (row : Fin width → ZMod p) :
    NativeLookupChallenge.compress (NativeLookupChallenge.powers y width) (List.ofFn row) =
      TupleHash.hash y row := by
  rw [NativeLookupChallenge.compress, fold_zip]
  simp only [NativeLookupChallenge.powers, powersFrom_eq, TupleHash.hash]

theorem tableAt_vectors (y : K) (table : Fin size → Fin width → ZMod p) :
    NativeLookupChallenge.tableAt (List.ofFn (fun i => List.ofFn (table i))) width y =
      List.ofFn (fun i => TupleHash.hash y (table i)) := by
  simp only [NativeLookupChallenge.tableAt, List.map_ofFn, Function.comp_def, compress_tuple]

private theorem zip_vectors {A B C : Type} {count : ℕ} (f : A → B → C)
    (left : Fin count → A) (right : Fin count → B) :
    (List.ofFn left).zipWith f (List.ofFn right) = List.ofFn (fun i => f (left i) (right i)) := by
  induction count with
  | zero => rfl
  | succ count ih => rw [List.ofFn_succ, List.ofFn_succ, List.zipWith_cons_cons, ih, List.ofFn_succ]

private theorem fold_add (values : List K) (initial : K) :
    values.foldl (fun out value => out + value) initial = initial + values.sum := by
  induction values generalizing initial with
  | nil => simp
  | cons value tail ih => simp only [List.foldl_cons, ih, List.sum_cons, add_assoc]

theorem compress_vectors (weights : Fin size → K) (values : Fin size → ZMod p) :
    NativeLookupChallenge.compress (List.ofFn weights) (List.ofFn values) =
      ∑ i, weights i * algebraMap (ZMod p) K (values i) := by
  rw [NativeLookupChallenge.compress, fold_zip, zip_vectors, fold_add, zero_add, List.sum_ofFn]

variable [DecidableEq K]

/-- Literal native `table_sum`: zip with multiplicities, accumulating
inverse times the embedded base-field value. -/
def tableSum (policy : NativeLookupReciprocals.Policy) (r : K) (table : List K)
    (multiplicities : List (ZMod p)) : K :=
  NativeLookupChallenge.compress (NativeLookupReciprocals.inverses policy r table) multiplicities

/-- The sampler's actual public compressed table and inverse vector give
exactly the total used by the existing lookup pair arithmetic. -/
theorem tableSum_eq (policy : NativeLookupReciprocals.Policy) (r y : K)
    (table : Fin size → Fin width → ZMod p) (multiplicities : Fin size → ZMod p)
    (allowed : NativeLookupChallenge.allowed
      (NativeLookupChallenge.tableAt (List.ofFn (fun i => List.ofFn (table i))) width y) r = true) :
    tableSum policy r (NativeLookupChallenge.tableAt (List.ofFn (fun i => List.ofFn (table i))) width y)
      (List.ofFn multiplicities) = LookupPairArithmetic.tableSum r y table multiplicities := by
  rw [tableSum, NativeLookupReciprocals.inverses_correct _ _ _ allowed, tableAt_vectors, List.map_ofFn,
    compress_vectors, LookupPairArithmetic.tableSum]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _

/-- A completed compiled job supplies the native table total used by
soundness, once the trusted request is identified with its rectangular
public table. No new accepted-domain premise is supplied by the caller. -/
theorem completed_tableSum {degree : ℕ} (basis : Module.Basis (Fin degree) (ZMod p) K)
    (machine : NativeLookupBatch.Machine p K) (valid : NativeLookupBatch.Valid basis machine)
    (completed : NativeLookupBatch.Completed p K) (member : completed ∈ machine.completed)
    (y r : K) (weights compressed : List K) (transcript : NativeTranscript.Transcript)
    (finished : completed.selection.control = .finished y r weights compressed transcript)
    (table : Fin size → Fin width → ZMod p) (multiplicities : Fin size → ZMod p)
    (widthMatches : completed.job.request.width = width)
    (tableMatches : completed.job.request.rows = List.ofFn (fun i => List.ofFn (table i)))
    (policy : NativeLookupReciprocals.Policy) :
    tableSum policy r compressed (List.ofFn multiplicities) =
      LookupPairArithmetic.tableSum r y table multiplicities := by
  have selected := (valid.2 completed member).1.2.1
  unfold NativeLookupChallenge.SelectionValid at selected
  rw [finished] at selected
  have source : compressed =
      NativeLookupChallenge.tableAt (List.ofFn (fun i => List.ofFn (table i))) width y := by
    rw [selected.2.1, selected.1, widthMatches, tableMatches]
    rfl
  rw [source]
  apply tableSum_eq
  simpa only [source] using selected.2.2

end

end FormalProof4FHE.HasteBoots.NativeLookupArithmetic
