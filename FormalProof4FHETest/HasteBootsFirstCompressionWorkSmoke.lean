module
import all FormalProof4FHE.HasteBoots.CallerLookupWorkCoverage
import all FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability

namespace HasteBootsFirstCompressionWorkSmoke
open FormalProof4FHE.HasteBoots
open NativeFields (Goldilocks)
open NativeExtensionFields (Goldilocks3)
open NativeLookupRequestWire (Request)
noncomputable section

def request (repetitions : NativeUsizeMessage.Usize) : Request :=
  ⟨⟨⟨3,by decide⟩,⟨[⟨[0,1],by decide⟩,⟨[1,2],by decide⟩],by decide⟩,repetitions⟩,
    ⟨[⟨0,by decide⟩,⟨0,by decide⟩],by decide⟩⟩

/-- Maximal legal repetitions share one small original table payload; the
work bound must price actual stream exposures rather than replicate it. -/
theorem repetitions_share_payload :
    LookupRequestPayloadSize.complexity (request ⟨2^64-1,by decide⟩) = 2 ∧
    LookupRequestPayloadSize.complexity (request ⟨1,by decide⟩) = 2 ∧
    (NativeLookupRequestWire.requestsCodec.encode ⟨[request ⟨2^64-1,by decide⟩],by decide⟩).length < 100 := by decide +kernel

/-- Width-one tuple compression is injective at every challenge. Its zero
polynomial degree does not require a positive miss-event floor. -/
theorem width_one_injective (y : Goldilocks3) : Function.Injective (TupleHash.hash (F := Goldilocks) y : (Fin 1 → Goldilocks) → Goldilocks3) := by
  intro left right equal
  have point : algebraMap Goldilocks Goldilocks3 (left 0) = algebraMap Goldilocks Goldilocks3 (right 0) := by
    simpa only [TupleHash.hash_eq_sum,Fin.sum_univ_one,Fin.val_zero,pow_zero,one_mul] using equal
  have same := (algebraMap Goldilocks Goldilocks3).injective point
  funext index
  have zero : index = 0 := Fin.eq_zero index
  rw [zero]
  exact same

def badSource : Fin 1 → Fin 2 → Goldilocks := fun _ column => if column.val = 0 then 0 else 1
def publicTable : Fin 1 → Fin 2 → Goldilocks := fun _ _ => 0

/-- A nonmember can pass the reciprocal relation at a compression collision
while the offset is in the native allowed domain. This exercises the event
being priced, rather than assuming that algebraic passage implies membership. -/
theorem collision_can_pass :
    (∃ position, ∀ row, badSource position ≠ publicTable row) ∧
    TupleLookupPair.Passes badSource publicTable (fun _ => (1 : Goldilocks3)) (0,1) ∧
    LookupPairChallengeBounds.Domain (fun row => TupleHash.hash (0 : Goldilocks3) (publicTable row)) 1 := by
  have sourceHash (index : Fin 1) : TupleHash.hash (0 : Goldilocks3) (badSource index) = 0 := by
    norm_num [TupleHash.hash_eq_sum,Fin.sum_univ_succ,badSource]
  have tableHash (index : Fin 1) : TupleHash.hash (0 : Goldilocks3) (publicTable index) = 0 := by
    norm_num [TupleHash.hash_eq_sum,Fin.sum_univ_succ,publicTable]
  constructor
  · refine ⟨0,fun row equal => ?_⟩
    have point := congrFun equal (1 : Fin 2)
    norm_num [badSource,publicTable] at point
  · constructor
    · refine ⟨fun _ => 1,?_,?_⟩
      · intro index
        simp [sourceHash]
      · norm_num [tableHash]
    · constructor
      · exact one_ne_zero
      · intro index
        change (1 : Goldilocks3) + TupleHash.hash 0 (publicTable index) ≠ 0
        rw [tableHash]
        simp

end
end HasteBootsFirstCompressionWorkSmoke
