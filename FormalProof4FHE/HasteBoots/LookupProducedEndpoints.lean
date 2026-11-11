module
public import FormalProof4FHE.HasteBoots.NativeGoldLookupProducer
@[expose] public section

/-! Successful native raw production identifies its literal first/last
retained draws and coefficient decoders, without supplied challenge values. -/
namespace FormalProof4FHE.HasteBoots.LookupProducedEndpoints
open NativeExtensionFields (Goldilocks3)
open NativeFieldRepresentation (GoldWord)
noncomputable section

theorem sources (width : ℕ) (rows : List (List GoldWord))
    (selection : NativeLookupChallenge.Machine Goldilocks3) (output : NativeGoldLookupProducer.Output)
    (produced : NativeGoldLookupProducer.produce width rows selection = some output) :
    NativeGoldLookupProducer.sourceWords selection = some (output.y,output.r) := by
  unfold NativeGoldLookupProducer.produce at produced
  obtain ⟨⟨y,r⟩,found,returned⟩ := Option.bind_eq_some_iff.mp produced
  dsimp only at returned
  split at returned
  · obtain ⟨inverses,_,same⟩ := Option.map_eq_some_iff.mp returned
    cases same
    exact found
  · contradiction

theorem draws (width : ℕ) (rows : List (List GoldWord))
    (selection : NativeLookupChallenge.Machine Goldilocks3) (output : NativeGoldLookupProducer.Output)
    (produced : NativeGoldLookupProducer.produce width rows selection = some output) :
    ∃ first last : NativeLookupChallenge.Draw Goldilocks3,
      selection.draws.head? = some first ∧ selection.draws.getLast? = some last ∧
      NativeGoldLookupProducer.decode first.coefficients.values = some output.y ∧
      NativeGoldLookupProducer.decode last.coefficients.values = some output.r := by
  have found := sources width rows selection output produced
  unfold NativeGoldLookupProducer.sourceWords at found
  split at found
  next =>
    obtain ⟨first,firstAt,found⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨last,lastAt,found⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨y,yDecode,found⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨r,rDecode,pair⟩ := Option.map_eq_some_iff.mp found
    have yEq : y = output.y := congrArg Prod.fst pair
    have rEq : r = output.r := congrArg Prod.snd pair
    exact ⟨first,last,firstAt,lastAt,yDecode.trans (congrArg some yEq),rDecode.trans (congrArg some rEq)⟩
  next => contradiction

end
end FormalProof4FHE.HasteBoots.LookupProducedEndpoints
