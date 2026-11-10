module
public import FormalProof4FHE.HasteBoots.AccumulatorQuerySplit
public import FormalProof4FHE.HasteBoots.MatrixCompression
@[expose] public section

/-! Deleting a fixed middle block of independently sampled matrix pairs keeps
exactly the fresh-query law for the retained prefix/suffix. The deleted draws
remain in the original computation; this is equality in distribution only. -/
namespace FormalProof4FHE.HasteBoots.MatrixQueryProjection
open OracleSpec OracleComp
open PackedSumcheckSubclaim (Query)
noncomputable section
variable {F : Type} {k : ℕ}

def drop : (skip keep : ℕ) → Query F k (keep+skip) → Query F k keep
  | 0, _, query => query
  | skip+1, keep, .cons _ tail => drop skip keep tail

def erase : (front skip back : ℕ) → Query F k ((back+skip)+front) → Query F k (back+front)
  | 0, skip, back, query => drop skip back query
  | front+1, skip, back, .cons pair tail => .cons pair (erase front skip back tail)

theorem drop_append {skip keep : ℕ} (first : Query F k skip) (last : Query F k keep) :
    drop skip keep (AccumulatorPackedQueries.append first last) = last := by
  induction first with
  | nil => rfl
  | cons pair tail ih => exact ih

theorem erase_append {front skip back : ℕ} (first : Query F k front) (middle : Query F k skip) (last : Query F k back) :
    erase front skip back (AccumulatorPackedQueries.append first (AccumulatorPackedQueries.append middle last)) =
      AccumulatorPackedQueries.append first last := by
  induction first with
  | nil => exact drop_append middle last
  | cons pair tail ih => exact congrArg (Query.cons pair) ih

def endpoint {c r : ℕ} (query : Query F k ((1+r)+c)) : Query F k (1+c) := erase c r 1 query

theorem endpoint_parts {c r : ℕ} (query : Query F k ((1+r)+c)) :
    endpoint query = AccumulatorPackedQueries.append (AccumulatorQuerySplit.parts query).1
      (.cons (AccumulatorQuerySplit.parts query).2.2 .nil) := by
  calc
    _ = endpoint (AccumulatorPackedQueries.whole (AccumulatorQuerySplit.parts query).1
        (AccumulatorQuerySplit.parts query).2.1 (AccumulatorQuerySplit.parts query).2.2) :=
      congrArg endpoint (AccumulatorQuerySplit.rebuild query).symm
    _ = _ := erase_append _ _ _

variable [Field F] [SampleableType (Fin k → F)]

theorem sample_drop (nodes : PackedSumcheckRound.Node k ↪ F) (skip keep : ℕ) :
    drop skip keep <$> MatrixCompression.sample nodes (keep+skip) =ᵈ MatrixCompression.sample nodes keep := by
  induction skip with
  | zero =>
    apply EvalDistEq.of_forall_prEvent_eq
    intro event
    simp only [drop, prEvent_norm]
    rfl
  | succ skip ih =>
    have ignored := OracleComp.EvalDistEq.bind_const ($ᵗ (Fin k → F))
      (drop skip keep <$> MatrixCompression.sample nodes (keep+skip))
    apply EvalDistEq.of_forall_prEvent_eq
    intro event
    have law := (ignored.trans ih).prEvent_eq event
    simp only [MatrixCompression.sample, prEvent_norm, drop] at law ⊢
    exact law

theorem sample_erase (nodes : PackedSumcheckRound.Node k ↪ F) (front skip back : ℕ) :
    erase front skip back <$> MatrixCompression.sample nodes ((back+skip)+front) =ᵈ
      MatrixCompression.sample nodes (back+front) := by
  induction front with
  | zero => exact sample_drop nodes skip back
  | succ front ih =>
    have retained := EvalDistEq.bind_right ($ᵗ (Fin k → F)) (fun challenge =>
      ih.map (Query.cons (PackedSumcheckRound.challengePair nodes challenge)))
    apply EvalDistEq.of_forall_prEvent_eq
    intro event
    have law := retained.prEvent_eq event
    simp only [MatrixCompression.sample, prEvent_norm, erase] at law ⊢
    exact law

theorem sample_endpoint (nodes : PackedSumcheckRound.Node k ↪ F) (c r : ℕ) :
    endpoint (c := c) (r := r) <$> MatrixCompression.sample nodes ((1+r)+c) =ᵈ
      MatrixCompression.sample nodes (1+c) := sample_erase nodes c r 1

end
end FormalProof4FHE.HasteBoots.MatrixQueryProjection
