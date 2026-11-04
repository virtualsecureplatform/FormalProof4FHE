module

public import FormalProof4FHE.HasteBoots.NativeLookupHelper
public import FormalProof4FHE.HasteBoots.ExtensionQuery
public import FormalProof4FHE.HasteBoots.FlatMatrixFold

@[expose] public section

/-!
# Native coefficient-helper packing and its PCS source

This models `packed_extension::table` at the field-value level. Coordinates
are copied in declared basis order and each row is padded to packed width.
The native checked geometry and exact flat address are explicit. Raw native
representatives, serialized leaf bytes, memory refinement and commitments
remain separate obligations.
-/

namespace FormalProof4FHE.HasteBoots.NativeHelperPacking

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] {degree : ℕ}

def coefficients (basis : Module.Basis (Fin degree) F K) (width : ℕ) (value : K) : Fin width → F :=
  fun lane => if meaningful : lane.val < degree then basis.equivFun value ⟨lane.val, meaningful⟩ else 0

def vector (basis : Module.Basis (Fin degree) F K) (width : ℕ) (value : K) : List F :=
  List.ofFn (coefficients basis width value)

theorem vector_length (basis : Module.Basis (Fin degree) F K) (width : ℕ) (value : K) :
    (vector basis width value).length = width := List.length_ofFn

theorem coefficients_padded (basis : Module.Basis (Fin degree) F K) (padding : ℕ) (value : K) :
    coefficients basis (degree + padding) value = PaddedExtension.encode (padding := padding) basis value := by
  funext lane
  refine Fin.addCases (fun i => ?_) (fun i => ?_) lane
  · simp [coefficients, PaddedExtension.encode, i.isLt]
  · simp [coefficients, PaddedExtension.encode]

def pack (basis : Module.Basis (Fin degree) F K) (width : ℕ) (values : List K) : List F :=
  values.flatMap (vector basis width)

theorem pack_length (basis : Module.Basis (Fin degree) F K) (width : ℕ) (values : List K) :
    (pack basis width values).length = values.length * width := by
  induction values with
  | nil => simp [pack]
  | cons value tail ih =>
    simp only [pack, List.flatMap_cons, List.length_append, vector_length] at *
    rw [ih, List.length_cons, Nat.succ_mul]
    exact Nat.add_comm _ _

/-- Every accessed packed entry has the exact row-major address. The
optional lookup succeeds, so no fallback coefficient is used. -/
theorem pack_get (basis : Module.Basis (Fin degree) F K) (width : ℕ) (values : List K)
    (row : ℕ) (present : row < values.length) (lane : Fin width) :
    (pack basis width values)[row * width + lane.val]? =
      some (coefficients basis width (values[row]) lane) := by
  induction values generalizing row with
  | nil => simp at present
  | cons value tail ih =>
    cases row with
    | zero =>
      rw [pack, List.flatMap_cons]
      simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getElem?_append_left (by rw [vector_length]; exact lane.isLt)]
      unfold vector
      rw [List.getElem?_eq_getElem (by simp), List.getElem_ofFn]
    | succ row =>
      rw [pack, List.flatMap_cons]
      change (vector basis width value ++ pack basis width tail)[(row + 1) * width + lane.val]? = _
      rw [List.getElem?_append_right (by rw [vector_length, Nat.add_mul, one_mul]; omega), vector_length]
      have address : (row + 1) * width + lane.val - width = row * width + lane.val := by
        rw [Nat.add_mul, one_mul]
        omega
      rw [address]
      exact ih row (by simpa using present)

structure Packed (F : Type) where
  numVars : ℕ
  width : ℕ
  values : List F
  deriving DecidableEq

def Geometry (degree numVars width valueCount : ℕ) : Prop :=
  degree ≠ 0 ∧ degree ≤ width ∧ width * width < 2 ^ 64 ∧ numVars < 64 ∧
    valueCount = 2 ^ numVars ∧ valueCount * width < 2 ^ 64

instance (degree numVars width valueCount : ℕ) : Decidable (Geometry degree numVars width valueCount) := by
  unfold Geometry
  infer_instance

inductive Error where
  | invalidGeometry | invalidIndex
  deriving DecidableEq

/-- Same admissible natural-number geometry as the native 64-bit helper
constructor. This does not claim checked Rust error-order correspondence. -/
def build (basis : Module.Basis (Fin degree) F K) (numVars width : ℕ) (values : List K) :
    Except Error (Packed F) :=
  if Geometry degree numVars width values.length then
    .ok ⟨numVars, width, pack basis width values⟩
  else .error .invalidGeometry

theorem build_ok_iff (basis : Module.Basis (Fin degree) F K) (numVars width : ℕ) (values : List K)
    (packed : Packed F) :
    build basis numVars width values = .ok packed ↔
      Geometry degree numVars width values.length ∧ packed = ⟨numVars, width, pack basis width values⟩ := by
  unfold build
  split <;> simp_all [eq_comm]

/-- `PackedTable::validate` geometry on the supported 64-bit target. -/
def Packed.Valid (packed : Packed F) : Prop :=
  packed.width ≠ 0 ∧ packed.numVars < 64 ∧
    packed.values.length = 2 ^ packed.numVars * packed.width ∧
    2 ^ packed.numVars * packed.width < 2 ^ 64

theorem build_valid (basis : Module.Basis (Fin degree) F K) (numVars width : ℕ) (values : List K)
    (packed : Packed F) (built : build basis numVars width values = .ok packed) : packed.Valid := by
  obtain ⟨geometry, rfl⟩ := (build_ok_iff basis numVars width values packed).mp built
  obtain ⟨positive, fits, square, varBound, length, capacity⟩ := geometry
  change width ≠ 0 ∧ numVars < 64 ∧ (pack basis width values).length = 2 ^ numVars * width ∧
    2 ^ numVars * width < 2 ^ 64
  refine ⟨by omega, varBound, ?_, ?_⟩
  · rw [pack_length, length]
  · rwa [length] at capacity

/-- A total view for the existing PCS interface. Its default getter is
proved unreachable on every successfully packed entry below. -/
def view (numVars width : ℕ) (flat : List F) : MatrixFold.Cube numVars → Fin width → F :=
  fun cell lane => flat[(FlatMatrixFold.index numVars cell).val * width + lane.val]?.getD 0

/-- Shape validation alone makes the view's fallback unreachable, even
for adversarial tables and arbitrary unused padding coefficients. -/
theorem view_valid_lookup (packed : Packed F) (valid : packed.Valid)
    (cell : MatrixFold.Cube packed.numVars) (lane : Fin packed.width) :
    packed.values[(FlatMatrixFold.index packed.numVars cell).val * packed.width + lane.val]? =
      some (view packed.numVars packed.width packed.values cell lane) := by
  have rowBound := (FlatMatrixFold.index packed.numVars cell).isLt
  have productBound := Nat.mul_le_mul (Nat.succ_le_of_lt rowBound) (Nat.le_refl packed.width)
  rw [Nat.succ_mul] at productBound
  have bound : (FlatMatrixFold.index packed.numVars cell).val * packed.width + lane.val < packed.values.length := by
    rw [valid.2.2.1]
    have laneBound := lane.isLt
    omega
  unfold view
  rw [List.getElem?_eq_getElem bound]
  rfl

theorem view_pack {numVars padding : ℕ} (basis : Module.Basis (Fin degree) F K) (values : List K)
    (length : values.length = 2 ^ numVars) (cell : MatrixFold.Cube numVars) :
    view numVars (degree + padding) (pack basis (degree + padding) values) cell =
      PaddedExtension.encode basis (values[(FlatMatrixFold.index numVars cell).val]'(by rw [length]; exact (FlatMatrixFold.index numVars cell).isLt)) := by
  funext lane
  unfold view
  rw [pack_get basis _ values _ (by rw [length]; exact (FlatMatrixFold.index numVars cell).isLt) lane]
  simp only [Option.getD_some, coefficients_padded]

/-- The actual flat helper source, queried in native Boolean order,
evaluates to the encoding of the original extension MLE. -/
theorem query_pack {numVars padding : ℕ} (basis : Module.Basis (Fin degree) F K)
    (values : List K) (length : values.length = 2 ^ numVars) (point : Fin numVars → K) :
    (ExtensionQuery.coefficientsQuery (padding := padding) basis point).evaluate
      (view numVars (degree + padding) (pack basis (degree + padding) values)) =
      PaddedExtension.encode basis (ExtensionQuery.evaluate numVars point (fun cell =>
        values[(FlatMatrixFold.index numVars cell).val]'(by rw [length]; exact (FlatMatrixFold.index numVars cell).isLt))) := by
  rw [ExtensionQuery.coefficients_evaluate]
  simp only [view_pack basis values length, PaddedExtension.decode_encode]

/-- An accepted wrong extension claim for this actual flat helper forces
a wrong base-field PCS claim, including the zero-variable post-map case. -/
theorem query_pack_false_claim {numVars padding : ℕ} (basis : Module.Basis (Fin degree) F K)
    (values : List K) (length : values.length = 2 ^ numVars) (point : Fin numVars → K)
    (expected : K) (claimed : Fin (degree + padding) → F)
    (accepted : PaddedExtension.element basis ((ExtensionQuery.coefficientsQuery basis point).finish claimed) = some expected)
    (wrong : expected ≠ ExtensionQuery.evaluate numVars point (fun cell =>
      values[(FlatMatrixFold.index numVars cell).val]'(by rw [length]; exact (FlatMatrixFold.index numVars cell).isLt))) :
    claimed ≠ (ExtensionQuery.coefficientsQuery basis point).query.fold
      (view numVars (degree + padding) (pack basis (degree + padding) values)) :=
  ExtensionQuery.false_claim basis _ _ _ expected claimed (query_pack basis values length point) accepted wrong


/-- Compose the proved native helper fill with coefficient packing.
Index failure is explicit, and geometry is checked before returning a table.
This is a field-level constructor, not checked Rust panic/work refinement. -/
def prepare (basis : Module.Basis (Fin degree) F K) (numVars width : ℕ)
    (policy : NativeLookupReciprocals.Policy) (r : K) (table : List K) (indices : List ℕ) :
    Except Error (Packed F) :=
  if Geometry degree numVars width (2 ^ numVars) then
    match NativeLookupHelper.fill (2 ^ numVars) (NativeLookupReciprocals.inverses policy r table) indices with
    | none => .error .invalidIndex
    | some values => build basis numVars width values
  else .error .invalidGeometry

theorem prepare_ok_iff (basis : Module.Basis (Fin degree) F K) (numVars width : ℕ)
    (policy : NativeLookupReciprocals.Policy) (r : K) (table : List K) (indices : List ℕ) (packed : Packed F) :
    prepare basis numVars width policy r table indices = .ok packed ↔
      ∃ values, NativeLookupHelper.fill (2 ^ numVars) (NativeLookupReciprocals.inverses policy r table) indices = some values ∧
        Geometry degree numVars width values.length ∧ packed = ⟨numVars, width, pack basis width values⟩ := by
  by_cases geometry : Geometry degree numVars width (2 ^ numVars)
  · cases filled : NativeLookupHelper.fill (2 ^ numVars) (NativeLookupReciprocals.inverses policy r table) indices with
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
    have length := NativeLookupHelper.fill_length _ _ _ _ filled
    exact geometry (by simpa only [length] using valid)

theorem prepare_valid (basis : Module.Basis (Fin degree) F K) (numVars width : ℕ)
    (policy : NativeLookupReciprocals.Policy) (r : K) (table : List K) (indices : List ℕ) (packed : Packed F)
    (prepared : prepare basis numVars width policy r table indices = .ok packed) : packed.Valid := by
  obtain ⟨values, _, geometry, packedEq⟩ := (prepare_ok_iff basis numVars width policy r table indices packed).mp prepared
  apply build_valid basis numVars width values packed
  exact (build_ok_iff basis numVars width values packed).mpr ⟨geometry, packedEq⟩

/-- The constructor's actual reciprocal helper vector is the source of
the PCS evaluation; its length and every packed entry are proved valid. -/
theorem prepare_query {numVars padding : ℕ} (basis : Module.Basis (Fin degree) F K)
    (policy : NativeLookupReciprocals.Policy) (r : K) (table : List K) (indices : List ℕ) (packed : Packed F)
    (prepared : prepare basis numVars (degree + padding) policy r table indices = .ok packed)
    (point : Fin numVars → K) :
    ∃ values, NativeLookupHelper.fill (2 ^ numVars) (NativeLookupReciprocals.inverses policy r table) indices = some values ∧
      ∃ length : values.length = 2 ^ numVars,
        (ExtensionQuery.coefficientsQuery (padding := padding) basis point).evaluate
          (view numVars (degree + padding) packed.values) =
          PaddedExtension.encode basis (ExtensionQuery.evaluate numVars point (fun cell =>
            values[(FlatMatrixFold.index numVars cell).val]'(by rw [length]; exact (FlatMatrixFold.index numVars cell).isLt))) := by
  obtain ⟨values, filled, _, rfl⟩ :=
    (prepare_ok_iff basis numVars (degree + padding) policy r table indices packed).mp prepared
  have length := NativeLookupHelper.fill_length _ _ _ _ filled
  exact ⟨values, filled, length, query_pack basis values length point⟩

/-- These concrete entry points preserve the native inverse-policy split. -/
def goldilocks (numVars width : ℕ) (r : NativeExtensionFields.Goldilocks3)
    (table : List NativeExtensionFields.Goldilocks3) (indices : List ℕ) :
    Except Error (Packed NativeFields.Goldilocks) := by
  classical
  exact prepare NativeExtensionFields.goldilocksBasis numVars width .individual r table indices

def babyBear (numVars width : ℕ) (r : NativeExtensionFields.BabyBear6)
    (table : List NativeExtensionFields.BabyBear6) (indices : List ℕ) :
    Except Error (Packed NativeFields.BabyBear) := by
  classical
  exact prepare NativeExtensionFields.babyBearBasis numVars width .batched r table indices

end

end FormalProof4FHE.HasteBoots.NativeHelperPacking
