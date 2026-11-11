module
public import FormalProof4FHE.HasteBoots.LookupGuardPoints
public import FormalProof4FHE.HasteBoots.NativeSharedLookupPreflightLink
@[expose] public section

/-! A view of one actual original identity guard. Every field is recovered
from native preflight, original preparation, scalar completion and guarding. -/
namespace FormalProof4FHE.HasteBoots.LookupIdentityView
open NativeSharedLookupStatement (Request Prepared)
open NativeSharedLookupPrelude (Ready guardInputs)
open NativeSharedLookupGuard (Checked Result)
open NativeLookupBindGeometry (Parameters)
open NativeSharedLookupProofShape (Values)
open NativeFieldRepresentation (GoldWord)
open NativeGoldExtensionArithmetic (Word)
open NativeExtensionFields (Goldilocks3)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open NativeScalarQueryShape (laneBits)
noncomputable section

structure View (padding row : ℕ) (n : NativeUsizeMessage.Usize) (job : Prepared)
    (claims : List NativeScalarBatchVerifier.SubClaim) (result : Result) (ordinal : ℕ) where
  checked : Checked
  checkedAt : result.checked[ordinal]? = some checked
  ordinalEq : checked.ordinal = ordinal
  requestEq : checked.request = job.tag.request.terminal
  inputs : Fin job.tag.request.columns → Fin (3+padding) → GoldWord
  inputsEq : List.ofFn (fun i => List.ofFn (inputs i)) = checked.values
  point : Fin (laneBits (3+padding)+row) → Word
  eqPoint : Fin (laneBits (3+padding)+row) → Word
  pointEq : List.ofFn point = result.point
  eqPointEq : List.ofFn eqPoint = checked.equalityPoint
  shape : NativeScalarQueryShape.check row (3+padding) (List.ofFn point).length = true
  dimension : n.val = laneBits (3+padding)+row
  claimAt : claims[2*ordinal+1]? = some checked.identityClaim
  claimPoint : checked.identityClaim.point = List.ofFn point
  producer : NativeLookupBatch.Completed NativeFields.goldilocksModulus Goldilocks3
  produced : NativeGoldLookupProducer.produce job.tag.request.columns job.tag.request.table producer.selection = some job.output
  shift : laneBits (3+padding)+row < 64
  enough : job.tag.request.terminal.logicalLength.val ≤ 2^(laneBits (3+padding)+row)
  terminal : NativeGoldTerminalQuery.constructedCheck row (3+padding) (List.ofFn eqPoint) (List.ofFn point)
    job.tag.request.terminal.logicalLength job.output.r (List.ofFn (fun i => List.ofFn (inputs i))) job.output.powers
    checked.helper checked.identityClaim.expected = some true

theorem recover {count padding : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (registry : List Parameters) (helper : Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper (List.ofFn requests) = some geometry)
    (openingCount : ℕ) (values : Values)
    (shape : NativeSharedLookupProofShape.check registry (List.ofFn requests) geometry openingCount values = true)
    (width : geometry.geometry.2.val = 3+padding)
    (rootFits : values.roots.length < 2^64) (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) (world : World)
    (ready : Ready geometry.geometry.1.val)
    (prepared : (OracleProgram.run (NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 values.multiplicities
      values.roots rootFits w lookupFuel equalityFuel transcript) world).run.1 = some ready)
    (proof : NativeScalarBatchPreflight.Proof) (fuel : ℕ) (claims : List NativeScalarBatchVerifier.SubClaim)
    (finished : (NativeScalarBatchVerifier.execute ready.statement proof fuel
      (NativeScalarBatchVerifier.initial ready.equality.transcript ready.statement proof) world).1.control = .finished claims)
    (sourceVars : ℕ) (result : Result)
    (passed : NativeSharedLookupGuard.guard (guardInputs requests ready values.sources values.helpers)
      claims sourceVars geometry.geometry.2.val = some result) (index : Fin ready.jobs.length) :
    ∃ view : View padding sourceVars geometry.geometry.1 (ready.jobs.get index) claims result index.val,
      view.producer ∈ (NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis w lookupFuel
        (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world).1.completed ∧
      view.producer.job = (ready.jobs.get index).tag.job ∧
      List.Forall₂ (fun slot value => values.sources[slot]? = some value)
        (ready.jobs.get index).tag.request.terminal.sourceSlots view.checked.values ∧
      ∃ draw, ready.machine.draws[index.val]? = some draw ∧ NativeGoldLookupEquality.DrawEvidence draw (List.ofFn view.eqPoint) := by
  obtain ⟨checked,checkedAt,ordinal,job,request,evidence,inputs,inputsEq,related⟩ :=
    LookupGuardSources.vectors fits requests registry helper geometry preflight openingCount values shape width rootFits
      w lookupFuel equalityFuel transcript world ready prepared claims sourceVars result passed index
  have member := List.mem_of_getElem? checkedAt
  have passedWidth := passed
  rw [width] at passedWidth
  obtain ⟨dimension,point,eqPoint,pointEq,eqPointEq,pointShape,claimPoint,draw,drawAt,drawEvidence⟩ :=
    LookupGuardPoints.recover fits requests geometry.geometry.1 values.multiplicities values.roots rootFits
      w lookupFuel equalityFuel transcript world ready prepared values.sources values.helpers proof fuel claims finished sourceVars result passedWidth checked member
  obtain ⟨producer,producerMember,producerJob,produced⟩ := LookupGuardProducer.protocol_producer fits requests geometry.geometry.1
    values.multiplicities values.roots rootFits w lookupFuel equalityFuel transcript world ready prepared index
  obtain ⟨bound,first,accepted,head⟩ := NativeSharedLookupBody.finished_preflight ready.equality.transcript ready.statement proof fuel world claims finished
  have bounds := NativeSharedLookupPreflightLink.terminal_bounds fits requests registry helper geometry preflight values rootFits
    w lookupFuel equalityFuel transcript world ready prepared proof first bound accepted head fuel claims finished sourceVars result passed
  have pointLength : result.point.length = laneBits (3+padding)+sourceVars := by rw [← pointEq,List.length_ofFn]
  have shift : laneBits (3+padding)+sourceVars < 64 := by rw [← pointLength]; exact bounds.1
  have enough : (ready.jobs.get index).tag.request.terminal.logicalLength.val ≤ 2^(laneBits (3+padding)+sourceVars) := by
    rw [← request,← pointLength]; exact bounds.2 checked member
  have terminal := evidence.terminal
  rw [job,request,width,← inputsEq,← pointEq,← eqPointEq] at terminal
  have query := (NativeSharedLookupGuard.guard_spec _ claims sourceVars (3+padding) result passedWidth).query
  rw [← pointEq] at query
  have constructed : NativeGoldTerminalQuery.constructedCheck sourceVars (3+padding) (List.ofFn eqPoint) (List.ofFn point)
      (ready.jobs.get index).tag.request.terminal.logicalLength (ready.jobs.get index).output.r
      (List.ofFn (fun i => List.ofFn (inputs i))) (ready.jobs.get index).output.powers checked.helper checked.identityClaim.expected = some true := by
    rw [NativeGoldTerminalQuery.constructedCheck,query,Option.bind_some]
    exact terminal
  refine ⟨⟨checked,checkedAt,ordinal,request,inputs,inputsEq,point,eqPoint,pointEq,eqPointEq,pointShape,dimension,?_,claimPoint,
    producer,produced,shift,enough,constructed⟩,producerMember,producerJob,related,draw,?_,drawEvidence⟩
  · simpa only [ordinal] using evidence.identity
  · simpa only [ordinal] using drawAt

end
end FormalProof4FHE.HasteBoots.LookupIdentityView
