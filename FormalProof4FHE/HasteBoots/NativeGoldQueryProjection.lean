module

public import FormalProof4FHE.HasteBoots.NativeGoldCoefficientsQuery

@[expose] public section

/-!
# Actual query post-map and checked extension decoder

A successfully interpreted query carries its own post-map correspondence.
Applying the actual raw post-map and padding check therefore has the same
complete partial meaning as finishing that interpreted field query and
decoding. No source-dependent post-map certificate or padded-input premise
is introduced. Truthful-opening premises below are explicit; PCS acceptance
has not yet been connected to them.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldQueryProjection

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeGoldCoefficientsQuery
open scoped Matrix

noncomputable section

theorem interpret_post (width n : ℕ) (raw : Query) (query : ExtensionQuery.Broadcast Goldilocks width n)
    (interpreted : interpret width n raw = some query) : readPost width raw.post = some query.post := by
  unfold interpret at interpreted
  cases pairs : readPairs width n raw.pairs with
  | none => rw [pairs, Option.bind_none] at interpreted; contradiction
  | some values =>
    rw [pairs, Option.bind_some] at interpreted
    cases post : readPost width raw.post with
    | none => rw [post, Option.map_none] at interpreted; contradiction
    | some matrix =>
      rw [post, Option.map_some] at interpreted
      have same := congrArg ExtensionQuery.Broadcast.post (Option.some.inj interpreted)
      rw [← same]

theorem fieldApply_readPost (width : ℕ) (raw : Option NativeGoldMatrix.Matrix)
    (post : Option (_root_.Matrix (Fin width) (Fin width) Goldilocks))
    (positive : width ≠ 0) (read : readPost width raw = some post) (values : Fin width → Goldilocks) :
    NativeGoldPostMap.fieldApply width raw values = some (post.elim values (fun matrix => matrix *ᵥ values)) := by
  cases raw with
  | none =>
    have same : post = none := (Option.some.inj read).symm
    rw [same, NativeGoldPostMap.fieldApply, ite_eq_right positive, Option.elim_none]
  | some matrix =>
    by_cases valid : NativeGoldMatrix.validate matrix width = true
    · simp only [readPost, readMatrix, dite_eq_left valid, Option.map_some] at read
      have same := (Option.some.inj read).symm
      rw [same, NativeGoldPostMap.fieldApply, ite_eq_right positive, dite_eq_left valid, Option.elim_some]
    · simp only [readPost, readMatrix, dite_eq_right valid, Option.map_none] at read
      contradiction

/-- Complete success/failure correspondence on the actual returned query's
post-map and every original claimed input lane. -/
theorem query_project_value {padding n : ℕ} (raw : Query)
    (query : ExtensionQuery.Broadcast Goldilocks (3 + padding) n)
    (interpreted : interpret (3 + padding) n raw = some query) (input : Fin (3 + padding) → GoldWord)
    (fits : (3 + padding) * (3 + padding) < 2 ^ 64) :
    (NativeGoldPostMap.project (3 + padding) raw.post (List.ofFn input)).map goldExtensionValue =
      PaddedExtension.element goldilocksBasis (query.finish (fun i => goldValue (input i))) := by
  rw [NativeGoldPostMap.project_value _ _ fits,
    fieldApply_readPost _ _ query.post (by omega) (interpret_post _ _ raw query interpreted), Option.bind_some]
  cases post : query.post with
  | none => simp only [ExtensionQuery.Broadcast.finish, post, Option.elim_none]
  | some matrix => simp only [ExtensionQuery.Broadcast.finish, post, Option.elim_some]

/-- The actual helper constructor is used before its returned post-map is
applied and checked; zero-variable helper projection is retained. -/
theorem coefficientsQuery_project_value {padding n : ℕ} (point : Fin n → Word)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true) (input : Fin (3 + padding) → GoldWord) :
    ((coefficientsQuery (3 + padding) (List.ofFn point)).bind (fun raw =>
      NativeGoldPostMap.project (3 + padding) raw.post (List.ofFn input))).map goldExtensionValue =
        PaddedExtension.element goldilocksBasis
          ((ExtensionQuery.coefficientsQuery (padding := padding) goldilocksBasis (fun i => goldExtensionValue (point i))).finish
            (fun i => goldValue (input i))) := by
  rw [coefficientsQuery_success _ _ shape, Option.bind_some]
  exact query_project_value _ _ (interpret_built point shape) input ((NativeGoldProjection.dimensions_iff _).mp shape).2

/-- Conditional decoding of a truthful original helper opening. This premise
is not an assertion that native PCS acceptance has already been refined. -/
theorem coefficientsQuery_project_truth {padding n : ℕ} (point : Fin n → Word)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true) (input : Fin (3 + padding) → GoldWord)
    (table : MatrixFold.Cube n → Fin (3 + padding) → Goldilocks)
    (correct : (fun i => goldValue (input i)) =
      (ExtensionQuery.coefficientsQuery (padding := padding) goldilocksBasis (fun i => goldExtensionValue (point i))).query.fold table) :
    ((coefficientsQuery (3 + padding) (List.ofFn point)).bind (fun raw =>
      NativeGoldPostMap.project (3 + padding) raw.post (List.ofFn input))).map goldExtensionValue = some
        (ExtensionQuery.evaluate n (fun i => goldExtensionValue (point i))
          (fun cell => PaddedExtension.decode goldilocksBasis (table cell))) := by
  rw [coefficientsQuery_project_value point shape input, correct, ← ExtensionQuery.Broadcast.evaluate,
    ExtensionQuery.coefficients_evaluate, PaddedExtension.element_encode]

end

end FormalProof4FHE.HasteBoots.NativeGoldQueryProjection
