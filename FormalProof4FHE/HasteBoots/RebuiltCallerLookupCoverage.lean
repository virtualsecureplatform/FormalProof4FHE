module
public import FormalProof4FHE.HasteBoots.RebuiltJobPublicGeometry
public import FormalProof4FHE.HasteBoots.CallerCompressionRecovery
public import FormalProof4FHE.HasteBoots.LookupInitialPairedWork
@[expose] public section

/-! Original public tuple nonmembership reduces to an original compression
miss, an original reciprocal numerator miss, or the already priced native
arithmetic failure. Validated table shape and literal multiplicities follow
from rebuilt execution and native proof checks, not supplied row/count flags. -/
namespace FormalProof4FHE.HasteBoots.RebuiltCallerLookupCoverage
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open NativeSharedLookupValues (Policy)
open NativeGoldBatchOpening (Opening)
open NativeFields (Goldilocks goldilocksModulus)
open NativeExtensionFields (Goldilocks3)
open InputIndexedOracle (World)
open OracleProgram (Program run)
noncomputable section
local instance : CharP Goldilocks3 goldilocksModulus :=
  charP_of_injective_algebraMap (algebraMap Goldilocks Goldilocks3).injective goldilocksModulus

variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : AllocatedFamilyFunctions.Allocation ctx}
    {program : Program A} {world : World}

def tuples (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : NativeRootMessage.Digest) :=
  LookupTupleTest.tuples (data.origin.ready.jobs.get data.index).tag.request
    (NativeScalarQueryShape.checked_power _ _ _ data.job.view.shape) data.job.view.enough
    (CanonicalAllocatedTables.sources allocation data.origin data.index data.job data.geometry dummy (run program world).run.2)

def table (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :=
  LookupTupleTest.publicRows (data.origin.ready.jobs.get data.index).tag.request

def counts (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :
    Fin (data.origin.ready.jobs.get data.index).tag.request.table.length → Goldilocks := fun row =>
  NativeFieldRepresentation.goldValue
    ((ctx.proof.values.multiplicities[(data.origin.ready.jobs.get data.index).tag.ordinal.val]?.getD [])[row.val]?.getD 0)

theorem counts_eq (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (values : Fin (data.origin.ready.jobs.get data.index).tag.request.table.length → NativeFieldRepresentation.GoldWord)
    (atValues : ctx.proof.values.multiplicities[(data.origin.ready.jobs.get data.index).tag.ordinal.val]? = some (List.ofFn values)) :
    counts data = fun row => NativeFieldRepresentation.goldValue (values row) := by
  funext row
  simp only [counts,atValues,Option.getD_some]
  rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using row.isLt),Option.getD_some,List.getElem_ofFn]

def Passes (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : NativeRootMessage.Digest) : Prop :=
  TupleLookupPair.Passes (tuples data dummy) (table data) (fun row => algebraMap Goldilocks Goldilocks3 (counts data row))
    (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y,
      NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.r)

def Nonmember (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : NativeRootMessage.Digest) : Prop :=
  ∃ position, ∀ row, tuples data dummy position ≠ table data row

def ReciprocalMiss (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : NativeRootMessage.Digest) : Prop :=
  let y := NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y
  let r := NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.r
  let source := fun position => TupleHash.hash y (tuples data dummy position)
  let publicHashes := fun row => TupleHash.hash y (table data row)
  let polynomial := ReciprocalPolynomial.numerator source publicHashes (fun row => algebraMap Goldilocks Goldilocks3 (counts data row))
  (∃ position, ∀ row, source position ≠ publicHashes row) ∧ polynomial ≠ 0 ∧ polynomial.eval r = 0

variable (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (policy : Policy) (original : Vector Request) (template : Context (Vector Opening)) (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (RebuiltLookupExecution.program policy original allocation.entries allocation.helperHandle allocation.references template
      data.chooseHelper data.chooseBatch data.memory) world).run.1 = .allocated (.verification ctx result))
include executed

theorem nonpassing_witness (dummy : NativeRootMessage.Digest) (inputs : SequencedCallerInputs.Inputs data)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame) (notPasses : ¬Passes data dummy) :
    Nonempty (LookupInitialPairedWork.Witness (Memory := Memory) ctx allocation program dummy world) := by
  have rectangular := RebuiltJobPublicGeometry.rectangular policy original allocation.entries allocation.helperHandle allocation.references template
    data.chooseHelper data.chooseBatch data.memory result executed data.origin data.index data.job
  obtain ⟨values,atValues⟩ := RebuiltJobPublicGeometry.counts_vector data.origin data.index
  have rows : (fun row column => NativeFieldRepresentation.goldValue
      (LookupValidatedPublicTable.rawRows (data.origin.ready.jobs.get data.index).tag.request rectangular row column)) = table data := by
    funext row column
    exact (LookupValidatedPublicTable.publicRows_eq _ rectangular row column).symm
  have countValues := counts_eq data values atValues
  refine ⟨LookupInitialPairedWork.ofNonpassing data dummy (LookupValidatedPublicTable.rawRows _ rectangular) values
    (LookupValidatedPublicTable.rawRows_exact _ rectangular).symm atValues inputs before bytes valid ?_⟩
  have rowPoint (row) (column) := congrFun (congrFun rows row) column
  have countPoint (row) := (congrFun countValues row).symm
  simp_rw [rowPoint,countPoint]
  exact notPasses

theorem reciprocal_miss (dummy : NativeRootMessage.Digest) (passed : Passes data dummy)
    (outside : ∃ position, ∀ row,
      TupleHash.hash (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y) (tuples data dummy position) ≠
      TupleHash.hash (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y) (table data row)) : ReciprocalMiss data dummy := by
  have rectangular := RebuiltJobPublicGeometry.rectangular policy original allocation.entries allocation.helperHandle allocation.references template
    data.chooseHelper data.chooseBatch data.memory result executed data.origin data.index data.job
  have domain := LookupValidatedPublicTable.produced_domain _ rectangular _ _ data.job.view.produced
  have small := RebuiltJobPublicGeometry.logical_lt_characteristic policy original allocation.entries allocation.helperHandle allocation.references template
    data.chooseHelper data.chooseBatch data.memory result executed data.origin data.index data.job
  have nonzero := ReciprocalPolynomial.numerator_ne_zero (p := goldilocksModulus)
    (fun position => TupleHash.hash (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y) (tuples data dummy position))
    (fun row => TupleHash.hash (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y) (table data row))
    (fun row => algebraMap Goldilocks Goldilocks3 (counts data row)) outside small
  refine ⟨outside,nonzero,?_⟩
  obtain ⟨helpers,valid,total⟩ := passed
  exact ReciprocalPolynomial.helper_identity_implies_root _ _ _ helpers _ valid domain.2 total

theorem nonmember_covered (dummy : NativeRootMessage.Digest) (inputs : SequencedCallerInputs.Inputs data)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame) (bad : Nonmember data dummy) :
    Nonempty (LookupInitialPairedWork.Witness (Memory := Memory) ctx allocation program dummy world) ∨
      CallerCompressionRecovery.Collision data dummy ∨ ReciprocalMiss data dummy := by
  classical
  by_cases passed : Passes data dummy
  · by_cases matched : ∀ position, ∃ row,
        TupleHash.hash (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y) (tuples data dummy position) =
        TupleHash.hash (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y) (table data row)
    · exact Or.inr (Or.inl ⟨bad,matched⟩)
    · have outside : ∃ position, ∀ row,
          TupleHash.hash (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y) (tuples data dummy position) ≠
          TupleHash.hash (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y) (table data row) := by
        simpa only [not_forall,not_exists] using matched
      exact Or.inr (Or.inr (reciprocal_miss data policy original template result executed dummy passed outside))
  · exact Or.inl (nonpassing_witness data policy original template result executed dummy inputs before bytes valid passed)

end
end FormalProof4FHE.HasteBoots.RebuiltCallerLookupCoverage
