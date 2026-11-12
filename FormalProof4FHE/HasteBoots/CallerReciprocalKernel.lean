module
public import FormalProof4FHE.HasteBoots.LookupReciprocalKernel
public import FormalProof4FHE.HasteBoots.RebuiltCallerLookupCoverage
public import FormalProof4FHE.HasteBoots.CallerLookupScalars
@[expose] public section

/-! The literal accepted offset of an original caller job witnesses a
reciprocal kernel on that exact stream. Statements here are frozen at the
reference world. Cross-world fixation and lifetime aggregation remain separate. -/
namespace FormalProof4FHE.HasteBoots.CallerReciprocalKernel
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open NativeSharedLookupValues (Policy)
open NativeGoldBatchOpening (Opening)
open NativeFields (Goldilocks goldilocksModulus)
open NativeExtensionFields (Goldilocks3)
open InputIndexedOracle (World Input law)
open OracleProgram (Program run runPrefix)
open MeasureTheory ProbabilityTheory
noncomputable section

variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : AllocatedFamilyFunctions.Allocation ctx}
    {program : Program A} {world : World}

def sources (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : NativeRootMessage.Digest) :=
  fun position => TupleHash.hash (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y)
    (RebuiltCallerLookupCoverage.tuples data dummy position)

def table (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :=
  fun row => TupleHash.hash (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y)
    (RebuiltCallerLookupCoverage.table data row)

def multiplicities (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :=
  fun row => algebraMap Goldilocks Goldilocks3 (RebuiltCallerLookupCoverage.counts data row)

def Event (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (dummy : NativeRootMessage.Digest) (input : Input) : World → Prop :=
  LookupReciprocalKernel.Event input (sources data dummy) (table data) (multiplicities data)

/-- No independent offset or earliest-read certificate is supplied. The
native retained last draw and complete caller history determine both. -/
theorem recover (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (dummy : NativeRootMessage.Digest) (miss : RebuiltCallerLookupCoverage.ReciprocalMiss data dummy) :
    ∃ last : NativeLookupChallenge.Draw Goldilocks3,
      data.job.view.producer.selection.draws.getLast? = some last ∧
      Nonempty (ProgramFirstStreamRead.First program world last.coefficients.phase.pending.input) ∧
      Event data dummy last.coefficients.phase.pending.input world := by
  obtain ⟨_,last,_,lastAt,_,collected,_,first⟩ := CallerLookupScalars.endpoints data
  obtain ⟨budget,collected⟩ := collected
  refine ⟨last,lastAt,first,budget,?_⟩
  rw [collected]
  exact ⟨miss.1,miss.2.2⟩

variable (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (policy : Policy) (original : Vector Request) (template : Context (Vector Opening)) (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (RebuiltLookupExecution.program policy original allocation.entries allocation.helperHandle allocation.references template
      data.chooseHelper data.chooseBatch data.memory) world).run.1 = .allocated (.verification ctx result))
include executed

/-- A bound for a reference world's frozen statement. This deliberately does
not assert that another caller on the same prefix has that statement. -/
theorem first_bound (dummy : NativeRootMessage.Digest) (input : Input)
    (first : ProgramFirstStreamRead.First program world input) :
    (law[|{other | (runPrefix first.position program other).run = (runPrefix first.position program world).run}])
      {other | Event data dummy input other} ≤
      (((data.origin.ready.jobs.get data.index).tag.request.terminal.logicalLength.val +
        (data.origin.ready.jobs.get data.index).tag.request.table.length-1 : ℕ) : ENNReal)/(goldilocksModulus^3 : ℕ) := by
  exact LookupReciprocalKernel.conditional_bound OracleProgramMachine.step
    (OracleProgram.prefix_replay first.position program) world dummy input first.selected
    (sources data dummy) (table data) (multiplicities data)
    (RebuiltJobPublicGeometry.logical_lt_characteristic policy original allocation.entries allocation.helperHandle allocation.references template
      data.chooseHelper data.chooseBatch data.memory result executed data.origin data.index data.job)

/-- Actual tuple nonmembership is covered by arithmetic, compression, or an
attained reciprocal stream with its earliest positive caller observation. -/
theorem nonmember_covered (dummy : NativeRootMessage.Digest) (inputs : SequencedCallerInputs.Inputs data)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame) (bad : RebuiltCallerLookupCoverage.Nonmember data dummy) :
    Nonempty (LookupInitialPairedWork.Witness (Memory := Memory) ctx allocation program dummy world) ∨
      CallerCompressionRecovery.Collision data dummy ∨
      ∃ last : NativeLookupChallenge.Draw Goldilocks3,
        data.job.view.producer.selection.draws.getLast? = some last ∧
        Nonempty (ProgramFirstStreamRead.First program world last.coefficients.phase.pending.input) ∧
        Event data dummy last.coefficients.phase.pending.input world := by
  rcases RebuiltCallerLookupCoverage.nonmember_covered data policy original template result executed dummy inputs before bytes valid bad with
    arithmetic | compression | reciprocal
  · exact Or.inl arithmetic
  · exact Or.inr (Or.inl compression)
  · exact Or.inr (Or.inr (recover data dummy reciprocal))

end
end FormalProof4FHE.HasteBoots.CallerReciprocalKernel
