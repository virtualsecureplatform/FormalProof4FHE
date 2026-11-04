module

public import FormalProof4FHE.HasteBoots.NativeGoldHelper

@[expose] public section

/-!
# Checked raw helper geometry and the existing PCS source

The result is the raw flat coefficient storage with its dimensions supplied
by the constructor arguments. Index and geometry failure are explicit in
this checked model; Rust panic/error order, row-code/NTT execution and
commitment construction remain separate obligations.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldHelperPrepared

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeGoldHelper (fill pack)
open NativeHelperPacking (Geometry Error)

def build (numVars width : ℕ) (values : List Word) : Except Error (List GoldWord) :=
  if Geometry 3 numVars width values.length then .ok (pack width values) else .error .invalidGeometry

def prepare (numVars width : ℕ) (inverses : List Word) (indices : List ℕ) : Except Error (List GoldWord) :=
  if Geometry 3 numVars width (2 ^ numVars) then
    match fill (2 ^ numVars) inverses indices with
    | none => .error .invalidIndex
    | some values => build numVars width values
  else .error .invalidGeometry

theorem build_ok_iff (numVars width : ℕ) (values : List Word) (flat : List GoldWord) :
    build numVars width values = .ok flat ↔
      Geometry 3 numVars width values.length ∧ flat = pack width values := by
  unfold build
  split <;> simp_all [eq_comm]

theorem prepare_ok_iff (numVars width : ℕ) (inverses : List Word) (indices : List ℕ) (flat : List GoldWord) :
    prepare numVars width inverses indices = .ok flat ↔
      ∃ values, fill (2 ^ numVars) inverses indices = some values ∧
        Geometry 3 numVars width values.length ∧ flat = pack width values := by
  by_cases geometry : Geometry 3 numVars width (2 ^ numVars)
  · cases filled : fill (2 ^ numVars) inverses indices with
    | none => simp [prepare, geometry, filled]
    | some values =>
      simp only [prepare, geometry, ite_true, filled]
      rw [build_ok_iff]
      constructor
      · rintro ⟨valid, rfl⟩
        exact ⟨values, rfl, valid, rfl⟩
      · rintro ⟨other, same, valid, packedEq⟩
        have equal := Option.some.inj same
        subst other
        exact ⟨valid, packedEq⟩
  · simp only [prepare, geometry, ite_false, reduceCtorEq, false_iff]
    rintro ⟨values, filled, valid, _⟩
    have length := NativeGoldHelper.fill_length _ _ _ _ filled
    exact geometry (by simpa only [length] using valid)

theorem prepare_length (numVars width : ℕ) (inverses : List Word) (indices : List ℕ) (flat : List GoldWord)
    (prepared : prepare numVars width inverses indices = .ok flat) :
    flat.length = 2 ^ numVars * width ∧ flat.length < 2 ^ 64 := by
  obtain ⟨values, filled, geometry, rfl⟩ := (prepare_ok_iff numVars width inverses indices flat).mp prepared
  have length := NativeGoldHelper.fill_length _ _ _ _ filled
  rw [NativeGoldHelper.pack_length, length]
  exact ⟨rfl, by simpa only [length] using geometry.2.2.2.2.2⟩

noncomputable section

theorem prepare_valid (numVars width : ℕ) (inverses : List Word) (indices : List ℕ) (flat : List GoldWord)
    (prepared : prepare numVars width inverses indices = .ok flat) :
    (NativeHelperPacking.Packed.mk numVars width (flat.map goldValue)).Valid := by
  obtain ⟨values, _, geometry, _⟩ := (prepare_ok_iff numVars width inverses indices flat).mp prepared
  have length := prepare_length numVars width inverses indices flat prepared
  change width ≠ 0 ∧ numVars < 64 ∧ (flat.map goldValue).length = 2 ^ numVars * width ∧
    2 ^ numVars * width < 2 ^ 64
  refine ⟨by have enough := geometry.2.1; omega, geometry.2.2.2.1, ?_, ?_⟩
  · simpa only [List.length_map] using length.1
  · simpa only [length.1] using length.2

/-- Raw stored rows denote precisely the existing basis-packed table. -/
theorem build_value (numVars width : ℕ) (values : List Word) :
    (build numVars width values).map (List.map goldValue) =
      (NativeHelperPacking.build goldilocksBasis numVars width (values.map goldExtensionValue)).map
        NativeHelperPacking.Packed.values := by
  simp only [build, NativeHelperPacking.build, List.length_map]
  split <;> simp only [Except.map, NativeGoldHelper.pack_value]

/-- Successful or failed raw preparation projects to the existing semantic
constructor for the exact supplied individual reciprocal vector. -/
theorem prepare_value (numVars width : ℕ) (inverses : List Word) (indices : List ℕ)
    (r : Goldilocks3) (table : List Goldilocks3)
    (related : inverses.map goldExtensionValue = NativeLookupReciprocals.inverses .individual r table) :
    (prepare numVars width inverses indices).map (List.map goldValue) =
      (NativeHelperPacking.prepare goldilocksBasis numVars width .individual r table indices).map
        NativeHelperPacking.Packed.values := by
  have projection := NativeGoldHelper.fill_value (2 ^ numVars) inverses indices
  rw [related] at projection
  by_cases geometry : Geometry 3 numVars width (2 ^ numVars)
  · simp only [prepare, NativeHelperPacking.prepare, geometry, ite_true]
    cases filled : fill (2 ^ numVars) inverses indices with
    | none =>
      rw [filled, Option.map_none] at projection
      rw [← projection]
      rfl
    | some values =>
      rw [filled, Option.map_some] at projection
      rw [← projection]
      exact build_value numVars width values
  · simp only [prepare, NativeHelperPacking.prepare, geometry, ite_false]
    rfl

/-- The query evaluates the exact successfully filled raw helper, with the
same row-major coefficient source used by the existing PCS proof. -/
theorem prepare_query {numVars padding : ℕ} (inverses : List Word) (indices : List ℕ) (flat : List GoldWord)
    (prepared : prepare numVars (3 + padding) inverses indices = .ok flat)
    (point : Fin numVars → Goldilocks3) :
    ∃ values, fill (2 ^ numVars) inverses indices = some values ∧
      ∃ length : values.length = 2 ^ numVars,
        (ExtensionQuery.coefficientsQuery (padding := padding) goldilocksBasis point).evaluate
          (NativeHelperPacking.view numVars (3 + padding) (flat.map goldValue)) =
          PaddedExtension.encode goldilocksBasis (ExtensionQuery.evaluate numVars point (fun cell =>
            goldExtensionValue (values[(FlatMatrixFold.index numVars cell).val]'(by
              rw [length]; exact (FlatMatrixFold.index numVars cell).isLt)))) := by
  obtain ⟨values, filled, _, rfl⟩ := (prepare_ok_iff numVars (3 + padding) inverses indices flat).mp prepared
  have length := NativeGoldHelper.fill_length _ _ _ _ filled
  refine ⟨values, filled, length, ?_⟩
  rw [NativeGoldHelper.pack_value]
  have query := NativeHelperPacking.query_pack (padding := padding) goldilocksBasis (values.map goldExtensionValue)
    (by simpa only [List.length_map] using length) point
  simpa only [List.getElem_map] using query

/-- An accepted wrong extension claim for the actual raw helper forces a
wrong base-field PCS claim. This includes zero-variable post-map queries. -/
theorem prepare_false_claim {numVars padding : ℕ} (inverses : List Word) (indices : List ℕ) (flat : List GoldWord)
    (prepared : prepare numVars (3 + padding) inverses indices = .ok flat)
    (point : Fin numVars → Goldilocks3) :
    ∃ values, fill (2 ^ numVars) inverses indices = some values ∧
      ∃ length : values.length = 2 ^ numVars,
        ∀ (expected : Goldilocks3) (claimed : Fin (3 + padding) → Goldilocks),
          PaddedExtension.element goldilocksBasis
            ((ExtensionQuery.coefficientsQuery goldilocksBasis point).finish claimed) = some expected →
          expected ≠ ExtensionQuery.evaluate numVars point (fun cell =>
            goldExtensionValue (values[(FlatMatrixFold.index numVars cell).val]'(by
              rw [length]; exact (FlatMatrixFold.index numVars cell).isLt))) →
          claimed ≠ (ExtensionQuery.coefficientsQuery goldilocksBasis point).query.fold
            (NativeHelperPacking.view numVars (3 + padding) (flat.map goldValue)) := by
  obtain ⟨values, filled, length, query⟩ := prepare_query inverses indices flat prepared point
  exact ⟨values, filled, length, fun expected claimed accepted wrong =>
    ExtensionQuery.false_claim goldilocksBasis _ _ _ expected claimed query accepted wrong⟩

/-- The initialized sampler's actual raw inverse vector supplies helper
preparation, including matching failure paths, without an inverse certificate. -/
theorem executed_preparation_value (w fuel : ℕ) (actions : List (NativeLookupBatch.Action goldilocksModulus))
    (initialTranscript : NativeTranscript.Transcript) (world : InputIndexedOracle.World)
    (completed : NativeLookupBatch.Completed goldilocksModulus Goldilocks3)
    (member : completed ∈ (NativeLookupBatch.execute goldilocksBasis w fuel
      (NativeLookupBatch.initial actions initialTranscript) world).1.completed)
    (y r : Goldilocks3) (weights table : List Goldilocks3) (transcript : NativeTranscript.Transcript)
    (finished : completed.selection.control = .finished y r weights table transcript)
    (rows : List (List GoldWord)) (rowsMatch : completed.job.request.rows = rows.map (List.map goldValue))
    (numVars width : ℕ) (indices : List ℕ) :
    ∃ output, NativeGoldLookupProducer.produce completed.job.request.width rows completed.selection = some output ∧
      (prepare numVars width output.inverses indices).map (List.map goldValue) =
        (NativeHelperPacking.prepare goldilocksBasis numVars width .individual r table indices).map
          NativeHelperPacking.Packed.values := by
  obtain ⟨output, done, _, _, _, _, related, _⟩ := NativeGoldLookupProducer.executed_success
    w fuel actions initialTranscript world completed member y r weights table transcript finished rows rowsMatch
  exact ⟨output, done, prepare_value numVars width output.inverses indices r table related⟩

end

end FormalProof4FHE.HasteBoots.NativeGoldHelperPrepared
