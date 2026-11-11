module
public import FormalProof4FHE.HasteBoots.JobFamilyPosteriorMismatch
public import FormalProof4FHE.HasteBoots.AllocatedFactorSamples
@[expose] public section

/-! Observed factor samples at one actual world/input/original receipt
position. Reindexing a first-read witness changes only equal world/input
presentations and preserves its exact observation ordinal and request. -/
namespace FormalProof4FHE.HasteBoots.PositionedFactorSamples
open InputIndexedOracle (Input World)
open OracleProgram (Program run runPrefix)
open ProgramFirstStreamRead (First)
open LookupFactorFixation (Scalar Point)
open ScalarReceiptMatching (Position)
noncomputable section

def reindex {A : Type} {program : Program A} {world : World} {input : Input}
    (first : First program world input) (other : World) (target : Input) (world_eq : other = world) (input_eq : target = input) :
    First program other target where
  position := first.position
  offset := first.offset
  count := first.count
  next := first.next
  active := by rw [world_eq,input_eq]; exact first.active
  history := by rw [world_eq]; exact first.history
  fresh := by rw [world_eq,input_eq]; exact first.fresh
  positive := first.positive
  outputAt := by rw [world_eq,input_eq]; exact first.outputAt

structure ScalarAt {A : Type} (program : Program A) (world : World) (input : Input) (position : Position) where
  value : Scalar
  world_eq : value.view.reader.world = world
  input_eq : value.view.reader.entry.coefficients.phase.pending.input = input
  position_eq : value.position = position
  observed : ProgramFactorFixation.Observed program value.toSample

structure PointAt {A : Type} (program : Program A) (world : World) (input : Input) (position : Position) where
  value : Point
  world_eq : value.view.reader.world = world
  input_eq : value.view.reader.entry.coefficients.phase.pending.input = input
  position_eq : value.position = position
  observed : ProgramFactorFixation.Observed program value.toSample


def ScalarAt.reindex {A : Type} {program : Program A} {world : World} {input target : Input} {position slot : Position}
    (sample : ScalarAt program world input position) (input_eq : input = target) (position_eq : position = slot) : ScalarAt program world target slot :=
  ⟨sample.value,sample.world_eq,sample.input_eq.trans input_eq,sample.position_eq.trans position_eq,sample.observed⟩

def PointAt.reindex {A : Type} {program : Program A} {world : World} {input target : Input} {position slot : Position}
    (sample : PointAt program world input position) (input_eq : input = target) (position_eq : position = slot) : PointAt program world target slot :=
  ⟨sample.value,sample.world_eq,sample.input_eq.trans input_eq,sample.position_eq.trans position_eq,sample.observed⟩

theorem scalar {A : Type} (program : Program A) (position : ℕ) (world other : World) (input : Input) (slot : Position)
    (left : ScalarAt program world input slot) (right : ScalarAt program other input slot)
    (first : First program world input) (atFirst : first.position = position)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) :
    right.value.word = left.value.word ∨ ProgramReceiptCoverage.Bad program world ∨
      ProgramReceiptCoverage.Bad program other ∨ ProgramReceiptCollision.Bad program world := by
  let firstLeft := reindex first _ _ left.world_eq left.input_eq
  have input_eq := left.input_eq.trans right.input_eq.symm
  have position_eq := left.position_eq.trans right.position_eq.symm
  have receipt := ParentFactorFiber.receipt_packet (OracleProgram.prefix_replay position program) world other same
  have fiber : (ReceiptCandidateCompletion.extend (runPrefix firstLeft.position program) right.value.view.reader.world).run =
      (ReceiptCandidateCompletion.extend (runPrefix firstLeft.position program) left.value.view.reader.world).run := by
    change (ReceiptCandidateCompletion.extend (runPrefix first.position program) right.value.view.reader.world).run =
      (ReceiptCandidateCompletion.extend (runPrefix first.position program) left.value.view.reader.world).run
    rw [atFirst,left.world_eq,right.world_eq]
    exact receipt
  have fixed := ProgramFactorFixation.scalar_on_fiber program left.value right.value input_eq position_eq firstLeft left.observed right.observed fiber
  simpa only [ProgramFactorFixation.Bad,left.world_eq,right.world_eq] using fixed

theorem point {A : Type} (program : Program A) (position : ℕ) (world other : World) (input : Input) (slot : Position)
    (left : PointAt program world input slot) (right : PointAt program other input slot)
    (first : First program world input) (atFirst : first.position = position)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) :
    right.value.point = left.value.point ∨ ProgramReceiptCoverage.Bad program world ∨
      ProgramReceiptCoverage.Bad program other ∨ ProgramReceiptCollision.Bad program world := by
  let firstLeft := reindex first _ _ left.world_eq left.input_eq
  have input_eq := left.input_eq.trans right.input_eq.symm
  have position_eq := left.position_eq.trans right.position_eq.symm
  have receipt := ParentFactorFiber.receipt_packet (OracleProgram.prefix_replay position program) world other same
  have fiber : (ReceiptCandidateCompletion.extend (runPrefix firstLeft.position program) right.value.view.reader.world).run =
      (ReceiptCandidateCompletion.extend (runPrefix firstLeft.position program) left.value.view.reader.world).run := by
    change (ReceiptCandidateCompletion.extend (runPrefix first.position program) right.value.view.reader.world).run =
      (ReceiptCandidateCompletion.extend (runPrefix first.position program) left.value.view.reader.world).run
    rw [atFirst,left.world_eq,right.world_eq]
    exact receipt
  have fixed := ProgramFactorFixation.point_on_fiber program left.value right.value input_eq position_eq firstLeft left.observed right.observed fiber
  simpa only [ProgramFactorFixation.Bad,left.world_eq,right.world_eq] using fixed

end
end FormalProof4FHE.HasteBoots.PositionedFactorSamples
