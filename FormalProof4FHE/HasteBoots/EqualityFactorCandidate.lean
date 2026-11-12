module
public import FormalProof4FHE.HasteBoots.LoggedEqualityLookupFactors
@[expose] public section

/-! Original equality candidates fix complete canonical families and the
raw r/y factors on the same completed prefix fiber. The existing global
reference/receipt bad alternatives are retained, without per-factor charges. -/
namespace FormalProof4FHE.HasteBoots.EqualityFactorCandidate
open InputIndexedOracle (Input World)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open EqualityLookupFactorFixation (Scalar Side)
noncomputable section

structure At {A : Type} (program : Program A) (world : World) (input : Input) (ordinal : ℕ) (side : Side) where
  value : Scalar
  world_eq : value.world = world
  input_eq : value.view.input = input
  ordinal_eq : value.ordinal = ordinal
  side_eq : value.side = side
  observed : ProgramEqualityLookupFactors.Observed program value

def At.reindex {A : Type} {program : Program A} {world : World} {input target : Input} {ordinal slot : ℕ} {side : Side}
    (sample : At program world input ordinal side) (input_eq : input = target) (ordinal_eq : ordinal = slot) :
    At program world target slot side :=
  ⟨sample.value,sample.world_eq,sample.input_eq.trans input_eq,sample.ordinal_eq.trans ordinal_eq,sample.side_eq,sample.observed⟩

theorem at_fixed {A : Type} (program : Program A) (position : ℕ) (world other : World) (input : Input) (ordinal : ℕ) (side : Side)
    (left : At program world input ordinal side) (right : At program other input ordinal side)
    (first : ProgramFirstStreamRead.First program world input) (atFirst : first.position = position)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) :
    right.value.word = left.value.word ∨ ProgramReceiptCoverage.Bad program world ∨
      ProgramReceiptCoverage.Bad program other ∨ ProgramReceiptCollision.Bad program world := by
  let firstLeft := PositionedFactorSamples.reindex first _ _ left.world_eq left.input_eq
  have packet := ParentFactorFiber.receipt_packet (OracleProgram.prefix_replay position program) world other same
  have fiber : (ReceiptCandidateCompletion.extend (runPrefix firstLeft.position program) right.value.world).run =
      (ReceiptCandidateCompletion.extend (runPrefix firstLeft.position program) left.value.world).run := by
    change (ReceiptCandidateCompletion.extend (runPrefix first.position program) right.value.world).run =
      (ReceiptCandidateCompletion.extend (runPrefix first.position program) left.value.world).run
    rw [atFirst,left.world_eq,right.world_eq]
    exact packet
  have fixed := ProgramEqualityLookupFactors.scalar_on_fiber program left.value right.value
    (left.input_eq.trans right.input_eq.symm) (left.ordinal_eq.trans right.ordinal_eq.symm) (left.side_eq.trans right.side_eq.symm)
    firstLeft left.observed right.observed fiber
  simpa only [left.world_eq,right.world_eq] using fixed

structure Candidate {A : Type} (program : Program A) (position : ℕ) (world : World) where
  family : EqualityFamilyCandidate.Candidate program position world
  compression : At program world family.selection.family.input family.selection.index.val .compression
  offset : At program world family.selection.family.input family.selection.index.val .offset
  y : compression.value.word = (family.selection.origin.ready.jobs.get family.selection.index).output.y
  r : offset.value.word = (family.selection.origin.ready.jobs.get family.selection.index).output.r

theorem attach {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : EqualityFamilyCandidate.Candidate program position world)
    (success : (OracleProgram.run (NativeSharedLookupExecution.protocol NativeGoldBlockCode.description.row candidate.selection.ctx.registry candidate.selection.ctx.helper
      candidate.selection.ctx.parent candidate.selection.ctx.requests candidate.selection.ctx.proof candidate.selection.ctx.lookupFuel candidate.selection.ctx.equalityFuel
      candidate.selection.ctx.scalarFuel) world).run.1 = some (.bound candidate.selection.body))
    (observed : (OracleProgram.run (NativeSharedLookupExecution.protocol NativeGoldBlockCode.description.row candidate.selection.ctx.registry candidate.selection.ctx.helper
      candidate.selection.ctx.parent candidate.selection.ctx.requests candidate.selection.ctx.proof candidate.selection.ctx.lookupFuel candidate.selection.ctx.equalityFuel
      candidate.selection.ctx.scalarFuel) world).run.2.Sublist (OracleProgram.run program world).run.2) :
    ∃ result : Candidate program position world, result.family = candidate := by
  obtain ⟨view,input,groups⟩ := EqualityLookupReceiptView.recover candidate.selection.origin candidate.rootsFit candidate.draw
    (List.mem_of_getElem? candidate.drawAt)
  obtain ⟨compression,offset,leftView,rightView,leftWorld,rightWorld,leftOrdinal,rightOrdinal,leftSide,rightSide,y,r,leftObserved,rightObserved⟩ :=
    LoggedEqualityLookupFactors.recover candidate.selection.origin candidate.selection.job candidate.rootsFit program success observed view groups
  have leftInput : compression.view.input = candidate.selection.family.input := by rw [leftView,input,← candidate.input]
  have rightInput : offset.view.input = candidate.selection.family.input := by rw [rightView,input,← candidate.input]
  exact ⟨⟨candidate,⟨compression,leftWorld,leftInput,leftOrdinal,leftSide,leftObserved⟩,
    ⟨offset,rightWorld,rightInput,rightOrdinal,rightSide,rightObserved⟩,y,r⟩,rfl⟩

theorem fixed {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (input : left.family.selection.family.input = right.family.selection.family.input)
    (ordinal : left.family.selection.index.val = right.family.selection.index.val)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (good : JobReferenceFixation.Good program position world dummy) (safe : ¬JobReferenceFixation.CounterBad program other) :
    (HEq (EqualityFamilyCandidate.sources left.family dummy) (EqualityFamilyCandidate.sources right.family dummy) ∧
      HEq (EqualityFamilyCandidate.helpers left.family dummy) (EqualityFamilyCandidate.helpers right.family dummy)) ∧
      (right.family.selection.origin.ready.jobs.get right.family.selection.index).output.y =
        (left.family.selection.origin.ready.jobs.get left.family.selection.index).output.y ∧
      (right.family.selection.origin.ready.jobs.get right.family.selection.index).output.r =
        (left.family.selection.origin.ready.jobs.get left.family.selection.index).output.r := by
  have families := (EqualityFamilyCandidate.families_on_fiber program position world other left.family right.family dummy input ordinal same).resolve_right
    (JobReferenceFixation.family_bad_false program position world other dummy good safe)
  have compression := (at_fixed program position world other _ _ .compression left.compression
    (right.compression.reindex input.symm ordinal.symm) left.family.first left.family.first_position same).resolve_right
    (JobReferenceFixation.receipt_bad_false program position world other dummy good safe)
  have offset := (at_fixed program position world other _ _ .offset left.offset
    (right.offset.reindex input.symm ordinal.symm) left.family.first left.family.first_position same).resolve_right
    (JobReferenceFixation.receipt_bad_false program position world other dummy good safe)
  exact ⟨families,by simpa only [At.reindex,right.y,left.y] using compression,
    by simpa only [At.reindex,right.r,left.r] using offset⟩

end
end FormalProof4FHE.HasteBoots.EqualityFactorCandidate
