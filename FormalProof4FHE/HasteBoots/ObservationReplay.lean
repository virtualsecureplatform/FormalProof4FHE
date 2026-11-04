module

public import FormalProof4FHE.HasteBoots.NativeTranscript

@[expose] public section

/-!
# Counterfactual replay of mixed SHAKE/SHA-512 observations

A replay certificate includes truthfulness of the original log. Agreement
with an impossible log must not make replay vacuous. This whole-execution
property alone does not establish online causality: the oracle-program
interpreter proves it separately for every prefix and residual program.
-/

namespace FormalProof4FHE.HasteBoots.ObservationReplay

open InputIndexedOracle (Byte Input Coordinate World bytes sha512)
open NativeTranscript (Observation Execution)

def Matches (world : World) : Observation → Prop
  | .start _ => True
  | .output input offset output => bytes world input offset output.length = output
  | .hash input digest => List.ofFn (sha512 world input) = digest

def Agrees (world : World) (log : List Observation) : Prop :=
  ∀ entry ∈ log, Matches world entry

theorem agrees_append (world : World) (left right : List Observation) :
    Agrees world (left ++ right) ↔ Agrees world left ∧ Agrees world right := by
  simp [Agrees, List.mem_append, or_imp, forall_and]

structure Replayable {A : Type} (program : World → Execution A) : Prop where
  truthful : ∀ world, Agrees world (program world).run.2
  replay : ∀ world other, Agrees other (program world).run.2 →
    (program other).run = (program world).run

theorem run_bind {A B : Type} (first : Execution A) (next : A → Execution B) :
    (first >>= next).run =
      ((next first.run.1).run.1, first.run.2 ++ (next first.run.1).run.2) := by
  rcases first with ⟨value, log⟩
  rcases next value with ⟨result, tail⟩
  rfl

theorem constant {A : Type} (value : Execution A)
    (truthful : ∀ world, Agrees world value.run.2) : Replayable (fun _ => value) :=
  ⟨truthful, fun _ _ _ => rfl⟩

theorem pure_replay {A : Type} (value : A) : Replayable (fun _ => (pure value : Execution A)) := by
  apply constant
  intro world
  change Agrees world []
  simp [Agrees]

/-- The continuation may choose all later query inputs from the actual
earlier result, including its complete retained raw observations. -/
theorem bind_replay {A B : Type} {first : World → Execution A}
    {next : A → World → Execution B} (firstReplay : Replayable first)
    (nextReplay : ∀ value, Replayable (next value)) :
    Replayable (fun world => first world >>= fun value => next value world) := by
  constructor
  · intro world
    rw [run_bind]
    exact (agrees_append _ _ _).mpr
      ⟨firstReplay.truthful world, (nextReplay _).truthful world⟩
  · intro world other agree
    rw [run_bind] at agree
    obtain ⟨earlier, later⟩ := (agrees_append _ _ _).mp agree
    have firstSame := firstReplay.replay world other earlier
    have nextSame := (nextReplay _).replay world other later
    rw [run_bind, run_bind, firstSame, nextSame]

def start (input : Input) : Execution Unit := WriterT.mk ((), [.start input])

def read (world : World) (input : Input) (offset count : ℕ) : Execution Input :=
  let output := bytes world input offset count
  WriterT.mk (output, [.output input offset output])

/-- This hash primitive shares the same world and log as transcript reads.
The bridge to the existing native Merkle handler is still a separate task. -/
def hash (world : World) (input : Input) : Execution (Fin 64 → Byte) :=
  let digest := sha512 world input
  WriterT.mk (digest, [.hash input (List.ofFn digest)])

theorem start_replay (input : Input) : Replayable (fun _ => start input) := by
  apply constant
  intro world
  simp [Agrees, start, WriterT.run_mk, Matches]

theorem read_replay (input : Input) (offset count : ℕ) :
    Replayable (fun world => read world input offset count) := by
  constructor
  · intro world
    simp [Agrees, read, WriterT.run_mk, Matches, InputIndexedOracle.bytes_length]
  · intro world other agree
    have output := agree (.output input offset (bytes world input offset count)) (by simp [read, WriterT.run_mk])
    change bytes other input offset (bytes world input offset count).length = _ at output
    rw [InputIndexedOracle.bytes_length] at output
    simp only [read, WriterT.run_mk, output]

theorem hash_replay (input : Input) : Replayable (fun world => hash world input) := by
  constructor
  · intro world
    simp [Agrees, hash, WriterT.run_mk, Matches]
  · intro world other agree
    have output := agree (.hash input (List.ofFn (sha512 world input))) (by simp [hash, WriterT.run_mk])
    change List.ofFn (sha512 other input) = List.ofFn (sha512 world input) at output
    have same : sha512 other input = sha512 world input := List.ofFn_inj.mp output
    simp only [hash, WriterT.run_mk, same]

def coordinates : Observation → Finset Coordinate
  | .start _ => ∅
  | .output input offset output =>
      (Finset.range output.length).image (fun index => .inl (input, offset + index))
  | .hash input _ => (Finset.univ : Finset (Fin 64)).image (fun index => .inr (input, index))

def footprint (log : List Observation) : Finset Coordinate := log.toFinset.biUnion coordinates

/-- Changing an unreturned stream suffix, a different input's bytes, or an
unqueried hash digest preserves agreement with the existing observation. -/
theorem matches_of_same (world other : World) (entry : Observation) (matched : Matches world entry)
    (same : ∀ coordinate ∈ coordinates entry, other coordinate = world coordinate) : Matches other entry := by
  cases entry with
  | start input => trivial
  | output input offset output =>
    change bytes other input offset output.length = output
    change bytes world input offset output.length = output at matched
    apply Eq.trans ?_ matched
    unfold bytes InputIndexedOracle.block InputIndexedOracle.shake
    congr 1
    funext index
    exact same _ (Finset.mem_image.mpr ⟨index.val, Finset.mem_range.mpr index.isLt, rfl⟩)
  | hash input digest =>
    change List.ofFn (sha512 other input) = digest
    change List.ofFn (sha512 world input) = digest at matched
    rw [← matched]
    congr 1
    funext index
    exact same _ (Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩)

theorem agrees_of_same (world other : World) (log : List Observation) (truthful : Agrees world log)
    (same : ∀ coordinate ∈ footprint log, other coordinate = world coordinate) : Agrees other log := by
  intro entry member
  apply matches_of_same world other entry (truthful entry member)
  intro coordinate present
  exact same coordinate (Finset.mem_biUnion.mpr ⟨entry, List.mem_toFinset.mpr member, present⟩)

theorem same_of_matches (world other : World) (entry : Observation)
    (left : Matches world entry) (right : Matches other entry)
    (coordinate : Coordinate) (present : coordinate ∈ coordinates entry) :
    other coordinate = world coordinate := by
  cases entry with
  | start input => simp [coordinates] at present
  | output input offset output =>
    obtain ⟨index, member, rfl⟩ := Finset.mem_image.mp present
    have bound : index < output.length := Finset.mem_range.mp member
    change bytes world input offset output.length = output at left
    change bytes other input offset output.length = output at right
    have equal := List.ofFn_inj.mp (right.trans left.symm)
    exact congrFun equal ⟨index, bound⟩
  | hash input digest =>
    obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp present
    change List.ofFn (sha512 world input) = digest at left
    change List.ofFn (sha512 other input) = digest at right
    exact congrFun (List.ofFn_inj.mp (right.trans left.symm)) index

theorem same_of_agrees (world other : World) (log : List Observation)
    (left : Agrees world log) (right : Agrees other log) :
    ∀ coordinate ∈ footprint log, other coordinate = world coordinate := by
  intro coordinate present
  obtain ⟨entry, member, included⟩ := Finset.mem_biUnion.mp present
  have recorded := List.mem_toFinset.mp member
  exact same_of_matches world other entry (left entry recorded) (right entry recorded) coordinate included

theorem replay_of_same {A : Type} {program : World → Execution A} (certified : Replayable program)
    (world other : World)
    (same : ∀ coordinate ∈ footprint (program world).run.2, other coordinate = world coordinate) :
    (program other).run = (program world).run :=
  certified.replay world other (agrees_of_same world other _ (certified.truthful world) same)

/-- An adaptive execution's exact fiber is a finite coordinate-assignment
event in the original product sigma algebra, without normalizing success. -/
theorem fiber_eq_assignment {A : Type} {program : World → Execution A} (certified : Replayable program)
    (world : World) :
    {other | (program other).run = (program world).run} =
      InputIndexedOracle.assignment (footprint (program world).run.2) world := by
  ext other
  change (program other).run = (program world).run ↔
    ∀ coordinate ∈ footprint (program world).run.2, other coordinate = world coordinate
  constructor
  · intro same
    have truthful := certified.truthful other
    rw [same] at truthful
    exact same_of_agrees world other _ (certified.truthful world) truthful
  · exact replay_of_same certified world other

theorem fiber_measurable {A : Type} {program : World → Execution A} (certified : Replayable program)
    (world : World) : MeasurableSet {other | (program other).run = (program world).run} := by
  rw [fiber_eq_assignment certified world]
  exact InputIndexedOracle.assignment_measurable _ _

/-- Exact mass counts distinct returned bytes across both primitives.
Repeated reads are kept in the log but do not create fresh random bytes. -/
theorem fiber_mass {A : Type} {program : World → Execution A} (certified : Replayable program)
    (world : World) :
    InputIndexedOracle.law {other | (program other).run = (program world).run} =
      (256 : ENNReal)⁻¹ ^ (footprint (program world).run.2).card := by
  rw [fiber_eq_assignment certified world, InputIndexedOracle.assignment_mass]

/-- No resampling or security claim is assumed: this is pointwise invariance
under a single change outside the exact finite set of returned bytes. -/
theorem update_unobserved {A : Type} {program : World → Execution A} (certified : Replayable program)
    (world : World) (coordinate : Coordinate) (value : Byte)
    (unobserved : coordinate ∉ footprint (program world).run.2) :
    (program (Function.update world coordinate value)).run = (program world).run := by
  apply replay_of_same certified
  intro other member
  apply Function.update_of_ne
  intro equal
  subst other
  exact unobserved member

theorem fresh_recorded_byte_mass {A : Type} {program : World → Execution A}
    (certified : Replayable program) (world : World) (coordinate : Coordinate)
    (unobserved : coordinate ∉ footprint (program world).run.2) :
    InputIndexedOracle.law ({other | (program other).run = (program world).run} ∩
      {other | other coordinate = world coordinate}) =
      (256 : ENNReal)⁻¹ * InputIndexedOracle.law {other | (program other).run = (program world).run} := by
  rw [fiber_eq_assignment certified world]
  have merged : InputIndexedOracle.assignment (footprint (program world).run.2) world ∩
      {other | other coordinate = world coordinate} =
      InputIndexedOracle.assignment (insert coordinate (footprint (program world).run.2)) world := by
    ext other
    change ((∀ key ∈ footprint (program world).run.2, other key = world key) ∧
      other coordinate = world coordinate) ↔
      ∀ key ∈ insert coordinate (footprint (program world).run.2), other key = world key
    constructor
    · rintro ⟨old, new⟩ key member
      obtain equal | seen := Finset.mem_insert.mp member
      · subst key
        exact new
      · exact old key seen
    · intro all
      exact ⟨fun key member => all key (Finset.mem_insert.mpr (Or.inr member)),
        all coordinate (Finset.mem_insert_self _ _)⟩
  rw [merged]
  exact InputIndexedOracle.fresh_assignment_mass _ _ _ unobserved

/-- Exact extension of an adaptive execution fiber by any new byte value.
For whole-history use, the caller must supply the complete observed past,
including earlier hash/XOF calls. No division by successful mass or
success-floor premise is used. -/
theorem fresh_byte_mass {A : Type} {program : World → Execution A}
    (certified : Replayable program) (world : World) (coordinate : Coordinate) (value : Byte)
    (unobserved : coordinate ∉ footprint (program world).run.2) :
    InputIndexedOracle.law ({other | (program other).run = (program world).run} ∩
      {other | other coordinate = value}) =
      (256 : ENNReal)⁻¹ * InputIndexedOracle.law {other | (program other).run = (program world).run} := by
  let changed := Function.update world coordinate value
  have unchanged := update_unobserved certified world coordinate value unobserved
  have stillUnobserved : coordinate ∉ footprint (program changed).run.2 := by
    rw [unchanged]
    exact unobserved
  have extended := fresh_recorded_byte_mass certified changed coordinate stillUnobserved
  simpa only [unchanged, changed, Function.update_self] using extended

end FormalProof4FHE.HasteBoots.ObservationReplay
