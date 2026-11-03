module

public import FormalProof4FHE.HasteBoots.MatrixCompression
public import FormalProof4FHE.HasteBoots.NTTSourceQuery

@[expose] public section

/-!
# Canonical packed linear relations under one common matrix query

Trusted ordered coefficient/source pairs may repeat source indices and contain
zero coefficients. Literal left-to-right native residual accumulation agrees
with vector linear combination. Ordered matrix folding preserves that linear
combination even when query matrices do not commute. A false fixed family
passes one common fresh query within the compression error, without a union
over relations or sources. Authentication is supplied in the composed layer.
-/

open OracleSpec OracleComp
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.PackedLinear

noncomputable section

abbrev Relation (F Factor : Type) := List (F × Factor)

variable {F Factor : Type} [Field F] {b n : ℕ}

def evaluate (relation : Relation F Factor) (values : Factor → Fin b → F) : Fin b → F :=
  (relation.map fun term => term.1 • values term.2).sum

def residual (relation : Relation F Factor) (sources : Factor → MatrixFold.Cube n → Fin b → F) :
    MatrixFold.Cube n → Fin b → F := fun cell => evaluate relation (fun factor => sources factor cell)

def Holds (relations : List (Relation F Factor)) (sources : Factor → MatrixFold.Cube n → Fin b → F) : Prop :=
  ∀ relation ∈ relations, residual relation sources = 0

theorem foldl_evaluate (relation : Relation F Factor) (values : Factor → Fin b → F) (lane : Fin b) (initial : F) :
    relation.foldl (fun sum term => sum + term.1 * values term.2 lane) initial = initial + evaluate relation values lane := by
  induction relation generalizing initial with
  | nil => simp [evaluate]
  | cons term rest ih =>
    simp only [List.foldl_cons, ih, evaluate, List.map_cons, List.sum_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_assoc _ _ _

variable [DecidableEq F]

def check (relations : List (Relation F Factor)) (values : Factor → Fin b → F) : Bool :=
  relations.all fun relation => (List.ofFn fun lane : Fin b =>
    decide (relation.foldl (fun sum term => sum + term.1 * values term.2 lane) 0 = 0)).all id

theorem check_iff (relations : List (Relation F Factor)) (values : Factor → Fin b → F) :
    check relations values = true ↔ ∀ relation ∈ relations, evaluate relation values = 0 := by
  simp [check, foldl_evaluate, funext_iff]

omit [DecidableEq F] in
theorem fold_zero (query : Query F b n) : query.fold 0 = 0 := by
  simp only [Query.fold_eq_list, MatrixFold.foldAll_eq_weightedEvaluation,
    MatrixFold.weightedEvaluation, Pi.zero_apply, Matrix.mulVec_zero, Finset.sum_const_zero]

omit [DecidableEq F] in
theorem fold_add (query : Query F b n) (first second : MatrixFold.Cube n → Fin b → F) :
    query.fold (fun cell => first cell + second cell) = query.fold first + query.fold second := by
  simp only [Query.fold_eq_list, MatrixFold.foldAll_eq_weightedEvaluation,
    MatrixFold.weightedEvaluation, Matrix.mulVec_add, Finset.sum_add_distrib]

omit [DecidableEq F] in
theorem fold_residual (query : Query F b n) (relation : Relation F Factor)
    (sources : Factor → MatrixFold.Cube n → Fin b → F) :
    query.fold (residual relation sources) = evaluate relation (fun factor => query.fold (sources factor)) := by
  induction relation with
  | nil => change query.fold 0 = 0; exact fold_zero query
  | cons term rest ih =>
    change query.fold (fun cell => term.1 • sources term.2 cell + residual rest sources cell) =
      term.1 • query.fold (sources term.2) + evaluate rest (fun factor => query.fold (sources factor))
    rw [fold_add, NTTSourceQuery.fold_smul, ih]

theorem truthful_agreement (relations : List (Relation F Factor))
    (sources : Factor → MatrixFold.Cube n → Fin b → F) (query : Query F b n)
    (values : Factor → Fin b → F) (checked : check relations values = true)
    (truthful : ∀ factor, values factor = query.fold (sources factor)) :
    ∀ relation ∈ relations, query.fold (residual relation sources) = 0 := by
  intro relation member
  rw [fold_residual]
  have same : values = fun factor => query.fold (sources factor) := funext truthful
  rw [← same]
  exact (check_iff relations values).mp checked relation member

/-- Honest original tables pass the local linear check for every ordered
query, including zero variables; this part requires no randomness assumption. -/
theorem honest_check (relations : List (Relation F Factor))
    (sources : Factor → MatrixFold.Cube n → Fin b → F) (valid : Holds relations sources) (query : Query F b n) :
    check relations (fun factor => query.fold (sources factor)) = true := by
  apply (check_iff relations _).mpr
  intro relation member
  rw [← fold_residual, valid relation member, fold_zero]

variable [Fintype F] [SampleableType (Fin b → F)]

/-- Select a false relation before the query. All relations sharing that query
pay one compression error, regardless of the number of sources or summands. -/
theorem agreement_bound (nodes : PackedSumcheckRound.Node b ↪ F)
    (relations : List (Relation F Factor)) (sources : Factor → MatrixFold.Cube n → Fin b → F)
    (falseClaim : ¬Holds relations sources) :
    Pr{let query ← MatrixCompression.sample nodes n}[
      ∀ relation ∈ relations, query.fold (residual relation sources) = 0] ≤
      (n : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  classical
  obtain ⟨relation, bad⟩ := not_forall.mp falseClaim
  obtain ⟨member, wrong⟩ := not_forall.mp bad
  exact (prEvent_mono _ _ _ (fun _ agreed => agreed relation member)).trans
    (MatrixCompression.zero_bound nodes n (residual relation sources) wrong)

end

end FormalProof4FHE.HasteBoots.PackedLinear
