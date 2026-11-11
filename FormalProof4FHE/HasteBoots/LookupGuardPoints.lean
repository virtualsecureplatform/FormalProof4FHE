module
public import FormalProof4FHE.HasteBoots.LookupGuardSources
public import FormalProof4FHE.HasteBoots.NativeSharedLookupBody
@[expose] public section

/-! Recover both terminal points from their original native executions. The
scalar shape determines the full dimension; equality coordinates come from
the original equality draw rather than an independently supplied point. -/
namespace FormalProof4FHE.HasteBoots.LookupGuardPoints
open NativeSharedLookupStatement (Request)
open NativeSharedLookupPrelude (Ready guardInputs)
open NativeSharedLookupGuard (Checked Result)
open NativeFieldRepresentation (GoldWord)
open NativeGoldExtensionArithmetic (Word)
open NativeUsizeMessage (Usize)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open NativeScalarQueryShape (laneBits)
noncomputable section

theorem recover {count padding : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) (n : Usize)
    (multiplicities : List (List GoldWord)) (roots : List Digest) (rootFits : roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) (world : World) (ready : Ready n.val)
    (prepared : (OracleProgram.run (NativeSharedLookupPrelude.protocol fits requests n multiplicities roots rootFits
      w lookupFuel equalityFuel transcript) world).run.1 = some ready)
    (sources : List (List GoldWord)) (helpers : List Word) (proof : NativeScalarBatchPreflight.Proof)
    (fuel : ℕ) (claims : List NativeScalarBatchVerifier.SubClaim)
    (finished : (NativeScalarBatchVerifier.execute ready.statement proof fuel
      (NativeScalarBatchVerifier.initial ready.equality.transcript ready.statement proof) world).1.control = .finished claims)
    (sourceVars : ℕ) (result : Result)
    (passed : NativeSharedLookupGuard.guard (guardInputs requests ready sources helpers) claims sourceVars (3+padding) = some result)
    (checked : Checked) (member : checked ∈ result.checked) :
    n.val = laneBits (3+padding)+sourceVars ∧
      ∃ (point eqPoint : Fin (laneBits (3+padding)+sourceVars) → Word),
        List.ofFn point = result.point ∧ List.ofFn eqPoint = checked.equalityPoint ∧
        NativeScalarQueryShape.check sourceVars (3+padding) (List.ofFn point).length = true ∧
        checked.identityClaim.point = List.ofFn point ∧
        ∃ draw, ready.machine.draws[checked.ordinal]? = some draw ∧
          NativeGoldLookupEquality.DrawEvidence draw (List.ofFn eqPoint) := by
  obtain ⟨bound,first,accepted,head⟩ := NativeSharedLookupBody.finished_preflight ready.equality.transcript ready.statement proof fuel world claims finished
  have linked := NativeSharedLookupPrelude.protocol_scalar_link fits requests n multiplicities roots rootFits w lookupFuel equalityFuel
    transcript world ready prepared sources helpers proof first bound accepted head fuel claims finished sourceVars (3+padding) result passed
  have shape := NativeGoldScalarQuery.scalarQuery_checked sourceVars (3+padding) result.point result.pulled linked.1.guard.query
  have length := NativeScalarQueryShape.checked_length sourceVars (3+padding) result.point.length shape
  have dimension : n.val = laneBits (3+padding)+sourceVars := linked.2.1.symm.trans length.symm
  obtain ⟨draw,drawAt,evidence⟩ := linked.2.2 checked member
  have eqLength : checked.equalityPoint.length = laneBits (3+padding)+sourceVars := evidence.raw.length.trans dimension
  let point : Fin (laneBits (3+padding)+sourceVars) → Word := fun i => result.point[i.val]'(by rw [← length]; exact i.isLt)
  let eqPoint : Fin (laneBits (3+padding)+sourceVars) → Word := fun i => checked.equalityPoint[i.val]'(by rw [eqLength]; exact i.isLt)
  have pointEq : List.ofFn point = result.point := by
    apply List.ext_getElem (by rw [List.length_ofFn,length])
    intro i leftPresent rightPresent
    simp only [List.getElem_ofFn,point]
  have eqPointEq : List.ofFn eqPoint = checked.equalityPoint := by
    apply List.ext_getElem (by rw [List.length_ofFn,eqLength])
    intro i leftPresent rightPresent
    simp only [List.getElem_ofFn,eqPoint]
  refine ⟨dimension,point,eqPoint,pointEq,eqPointEq,?_,?_,draw,drawAt,?_⟩
  · rwa [pointEq]
  · exact (linked.1.claims checked member).2.2.2.1.trans pointEq.symm
  · rwa [eqPointEq]

end
end FormalProof4FHE.HasteBoots.LookupGuardPoints
