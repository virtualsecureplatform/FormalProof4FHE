module

public import FormalProof4FHE.HasteBoots.NativeLookupBatch

@[expose] public section

/-!
# Native lookup reciprocal arithmetic

The forward pass stores the product preceding each denominator. The reverse
pass uses one inverse of the total product and updates it in reverse order,
as in `packed_extension_lookup::batch_reciprocals`. Goldilocks and BabyBear
policies remain distinct: equality of field values does not imply equality
of lazy/Montgomery representatives, serialized bytes, work or helper roots.
-/

namespace FormalProof4FHE.HasteBoots.NativeLookupReciprocals

noncomputable section

variable {K : Type} [Field K]

/-- Product and ordered `(denominator, preceding product)` tape. -/
def forward : K → List K → K × List (K × K)
  | product, [] => (product, [])
  | product, value :: tail =>
      let later := forward (product * value) tail
      (later.1, (value, product) :: later.2)

/-- Reverse traversal; output positions remain in their original order.
The final first component is the inverse before the whole tape. -/
def backward : List (K × K) → K → K × List K
  | [], inverse => (inverse, [])
  | (value, product) :: tail, inverse =>
      let later := backward tail inverse
      (later.1 * value, (later.1 * product) :: later.2)

def Nonzero (values : List K) : Prop := ∀ value ∈ values, value ≠ 0

/-- The reverse loop invariant includes the running inverse, not merely
an asserted list of individually inverted outputs. -/
theorem backward_forward (product : K) (values : List K) (productNonzero : product ≠ 0)
    (valid : Nonzero values) :
    backward (forward product values).2 (forward product values).1⁻¹ =
      (product⁻¹, values.map (fun value => value⁻¹)) := by
  induction values generalizing product with
  | nil => rfl
  | cons value tail ih =>
    have nonzero := valid value (by simp)
    have tailValid : Nonzero tail := fun other member => valid other (by simp [member])
    simp only [forward, backward, ih (product * value) (mul_ne_zero productNonzero nonzero) tailValid]
    have first : (product * value)⁻¹ * value = product⁻¹ := by field_simp
    have second : (product * value)⁻¹ * product = value⁻¹ := by field_simp
    simp only [first, second, List.map_cons]

/-- The native empty branch performs no reciprocal computation. -/
def batch : List K → List K
  | [] => []
  | values@(_ :: _) =>
      let prepared := forward 1 values
      (backward prepared.2 prepared.1⁻¹).2

theorem batch_correct (values : List K) (valid : Nonzero values) :
    batch values = values.map (fun value => value⁻¹) := by
  cases values with
  | nil => rfl
  | cons value tail =>
    exact congrArg Prod.snd (backward_forward 1 (value :: tail) one_ne_zero valid)

inductive Policy where
  | individual | batched
  deriving DecidableEq

def tableReciprocals (policy : Policy) (values : List K) : List K :=
  match policy with
  | .individual => values.map (fun value => 1 / value)
  | .batched => batch values

theorem tableReciprocals_correct (policy : Policy) (values : List K) (valid : Nonzero values) :
    tableReciprocals policy values = values.map (fun value => value⁻¹) := by
  cases policy with
  | individual => simp only [tableReciprocals, one_div]
  | batched => exact batch_correct values valid

/-- Explicit native policies; these must not be interchanged in a claim
about serialized field representatives. -/
def goldilocks (values : List NativeExtensionFields.Goldilocks3) := tableReciprocals .individual values
def babyBear (values : List NativeExtensionFields.BabyBear6) := tableReciprocals .batched values

def denominators (r : K) (table : List K) : List K := table.map (fun value => r + value)

variable [DecidableEq K]

theorem allowed_nonzero (r : K) (table : List K) (allowed : NativeLookupChallenge.allowed table r = true) :
    Nonzero (denominators r table) := by
  intro denominator member
  obtain ⟨value, present, rfl⟩ := List.mem_map.mp member
  exact ((NativeLookupChallenge.allowed_iff table r).mp allowed).2 value present

def inverses (policy : Policy) (r : K) (table : List K) : List K :=
  tableReciprocals policy (denominators r table)

theorem inverses_correct (policy : Policy) (r : K) (table : List K)
    (allowed : NativeLookupChallenge.allowed table r = true) :
    inverses policy r table = table.map (fun value => (r + value)⁻¹) := by
  rw [inverses, tableReciprocals_correct policy _ (allowed_nonzero r table allowed)]
  simp only [denominators, List.map_map, Function.comp_def]

theorem inverses_length (policy : Policy) (r : K) (table : List K)
    (allowed : NativeLookupChallenge.allowed table r = true) :
    (inverses policy r table).length = table.length := by
  rw [inverses_correct policy r table allowed, List.length_map]

theorem inverses_get (policy : Policy) (r : K) (table : List K)
    (allowed : NativeLookupChallenge.allowed table r = true) (index : Fin table.length) :
    (inverses policy r table)[index.val]? = some ((r + table[index.val])⁻¹) := by
  rw [inverses_correct policy r table allowed, List.getElem?_eq_getElem (by simp)]
  simp only [List.getElem_map]

theorem inverse_identity (policy : Policy) (r : K) (table : List K)
    (allowed : NativeLookupChallenge.allowed table r = true) (index : Fin table.length) :
    (r + table[index.val]) * (inverses policy r table)[index.val]'(by
      rw [inverses_length policy r table allowed]
      exact index.isLt) = 1 := by
  simp only [inverses_correct policy r table allowed, List.getElem_map]
  exact mul_inv_cancel₀ (((NativeLookupChallenge.allowed_iff table r).mp allowed).2 _ (List.getElem_mem _))

end

end FormalProof4FHE.HasteBoots.NativeLookupReciprocals
