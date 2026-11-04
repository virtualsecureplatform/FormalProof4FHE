module

public import Mathlib.Probability.Independence.InfinitePi
public import ToMathlib.Probability.UniformOn
public import Mathlib.Data.List.OfFn

@[expose] public section

/-!
# One joint ideal SHAKE256/SHA-512 world

SHAKE is indexed by the complete absorbed input and output byte position.
SHA-512 uses a separate coordinate family in the same probability space.
Repeated queries, cloned readers, and split reads consult the same world;
method names and reader identities do not create fresh randomness.

This is the ideal-oracle law, not a claim about real SHA implementations or
adaptive transcript compilation. Native framing and the compiler are later
obligations. The world has the product sigma algebra, not the discrete one.
-/

namespace FormalProof4FHE.HasteBoots.InputIndexedOracle

open MeasureTheory ProbabilityTheory

noncomputable section

abbrev Byte := Fin 256
abbrev Input := List Byte
abbrev Coordinate := (Input × ℕ) ⊕ (Input × Fin 64)
abbrev World := Coordinate → Byte

instance byteMeasurableSpace : MeasurableSpace Byte := ⊤

def byteLaw : Measure Byte := uniformOn Set.univ

instance byte_probability : IsProbabilityMeasure byteLaw := by
  unfold byteLaw
  infer_instance

def law : Measure World := Measure.infinitePi (fun _ : Coordinate => byteLaw)

instance law_probability : IsProbabilityMeasure law := by
  unfold law
  infer_instance

/-- SHAKE bytes have no reader ID or call-site tag in their oracle key. -/
def shake (world : World) (input : Input) (position : ℕ) : Byte :=
  world (.inl (input, position))

/-- All hash users, including Merkle queries, share this same hash function. -/
def sha512 (world : World) (input : Input) : Fin 64 → Byte :=
  fun position => world (.inr (input, position))

def block (world : World) (input : Input) (offset count : ℕ) : Fin count → Byte :=
  fun index => shake world input (offset + index.val)

def bytes (world : World) (input : Input) (offset count : ℕ) : List Byte :=
  List.ofFn (block world input offset count)

theorem block_measurable (input : Input) (offset count : ℕ) :
    Measurable (fun world => block world input offset count) := by
  unfold block shake
  fun_prop

theorem hash_measurable (input : Input) : Measurable (fun world => sha512 world input) := by
  unfold sha512
  fun_prop

structure Reader where
  input : Input
  offset : ℕ
  deriving DecidableEq

def start (input : Input) : Reader := ⟨input, 0⟩

/-- A read advances only the cursor; it does not resample an oracle answer. -/
def read (world : World) (reader : Reader) (count : ℕ) : List Byte × Reader :=
  (bytes world reader.input reader.offset count, ⟨reader.input, reader.offset + count⟩)

theorem bytes_length (world : World) (input : Input) (offset count : ℕ) :
    (bytes world input offset count).length = count := by
  simp [bytes]

theorem bytes_append (world : World) (input : Input) (offset first second : ℕ) :
    bytes world input offset (first + second) =
      bytes world input offset first ++ bytes world input (offset + first) second := by
  unfold bytes block
  rw [List.ofFn_add]
  simp [Nat.add_assoc]

/-- Empty reads retain the cursor, including after earlier nonempty reads. -/
theorem read_zero (world : World) (reader : Reader) : read world reader 0 = ([], reader) := by
  cases reader
  simp [read, bytes]

/-- Splitting or coalescing consecutive reads preserves every returned byte
and the final cursor, for every world rather than merely almost surely. -/
theorem read_split (world : World) (reader : Reader) (first second : ℕ) :
    read world reader (first + second) =
      ((read world reader first).1 ++ (read world (read world reader first).2 second).1,
        (read world (read world reader first).2 second).2) := by
  simp [read, bytes_append, Nat.add_assoc]

/-- Restarting the same input reuses its prefix even after arbitrary other
queries: worlds are fixed, and a new reader starts at position zero. -/
theorem restart (world : World) (input : Input) (count : ℕ) :
    (read world (start input) count).1 = bytes world input 0 count := rfl

theorem byte_mass (value : Byte) : byteLaw {value} = (256 : ENNReal)⁻¹ := by
  simp [byteLaw, Byte]

/-- Independent uniform bytes are justified by distinct coordinates, never
by distinct method labels or reader-instance IDs. -/
theorem finite_coordinates {I : Type} [Fintype I] (coordinates : I → Coordinate)
    (distinct : Function.Injective coordinates) :
    law.map (fun world index => world (coordinates index)) =
      Measure.pi (fun _ : I => byteLaw) := by
  unfold law
  rw [Measure.map_infinitePi_infinitePi_of_inj distinct, Measure.infinitePi_eq_pi]

/-- The finite-vector marginal is exactly the uniform measure used by the
byte-sampler proofs. The distinctness premise must be discharged by callers. -/
theorem finite_coordinates_uniform {I : Type} [Fintype I] (coordinates : I → Coordinate)
    (distinct : Function.Injective coordinates) :
    law.map (fun world index => world (coordinates index)) =
      uniformOn (Set.univ : Set (I → Byte)) := by
  rw [finite_coordinates coordinates distinct]
  simpa only [byteLaw, Set.pi_univ] using
    (uniformOn_pi (f := fun _ : I => (Set.univ : Set Byte))).symm

theorem block_law (input : Input) (offset count : ℕ) :
    law.map (fun world => block world input offset count) =
      Measure.pi (fun _ : Fin count => byteLaw) := by
  apply finite_coordinates
  intro left right equal
  apply Fin.ext
  have positions := congrArg (fun coordinate : Coordinate =>
    coordinate.elim Prod.snd (fun _ => 0)) equal
  change offset + left.val = offset + right.val at positions
  omega

theorem hash_law (input : Input) :
    law.map (fun world => sha512 world input) =
      Measure.pi (fun _ : Fin 64 => byteLaw) := by
  apply finite_coordinates
  intro left right equal
  exact (Prod.mk.inj (Sum.inr.inj equal)).2

/-- Both primitives inhabit one joint law, including when their input byte
strings are equal. Different primitives use disjoint coordinate families. -/
theorem shake_hash_pair_law (shakeInput hashInput : Input) (offset : ℕ) (position : Fin 64) :
    law.map (fun world => (shake world shakeInput offset, sha512 world hashInput position)) =
      byteLaw.prod byteLaw := by
  apply Measure.infinitePi_map_eval_prod
  simp

/-- A finite exact history is an event in the product sigma algebra. -/
def assignment (seen : Finset Coordinate) (values : Coordinate → Byte) : Set World :=
  {world | ∀ coordinate ∈ seen, world coordinate = values coordinate}

theorem assignment_measurable (seen : Finset Coordinate) (values : Coordinate → Byte) :
    MeasurableSet (assignment seen values) := by
  have same : assignment seen values =
      ⋂ coordinate ∈ seen, (fun world : World => world coordinate) ⁻¹' {values coordinate} := by
    ext world
    simp [assignment]
  rw [same]
  exact MeasurableSet.biInter seen.countable_toSet fun coordinate _ =>
    (measurable_pi_apply coordinate) (measurableSet_singleton (values coordinate))

/-- Includes mixed hash/XOF prequeries, repeated-input positions, and any
finite subset of bytes. The cardinal counts distinct coordinates only. -/
theorem assignment_mass (seen : Finset Coordinate) (values : Coordinate → Byte) :
    law (assignment seen values) = (256 : ENNReal)⁻¹ ^ seen.card := by
  change Measure.infinitePi (fun _ : Coordinate => byteLaw)
    (Set.pi seen (fun coordinate => {values coordinate})) = _
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp [byte_mass]

/-- Fixed finite-history extension law. Adaptive-history disintegration and
the native compiler must still prove when their next coordinate is fresh. -/
theorem fresh_assignment_mass (seen : Finset Coordinate) (values : Coordinate → Byte)
    (coordinate : Coordinate) (fresh : coordinate ∉ seen) :
    law (assignment (insert coordinate seen) values) =
      (256 : ENNReal)⁻¹ * law (assignment seen values) := by
  rw [assignment_mass, assignment_mass, Finset.card_insert_of_notMem fresh, pow_succ']

end

end FormalProof4FHE.HasteBoots.InputIndexedOracle
