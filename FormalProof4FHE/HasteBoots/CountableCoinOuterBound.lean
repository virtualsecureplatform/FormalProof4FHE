module
public import FormalProof4FHE.HasteBoots.PrivateCoinLifetime
@[expose] public section

/-! Measurable countable strategy selection lifts arbitrary section events
using measurable hulls, retaining the original coin mass without a support
factor. No joint or section event measurability is supplied by the caller. -/
namespace FormalProof4FHE.HasteBoots.CountableCoinOuterBound
open MeasureTheory
open InputIndexedOracle (World law)
noncomputable section

theorem bound {Coins Choices : Type} [MeasurableSpace Coins] [MeasurableSpace Choices]
    [Countable Choices] [MeasurableSingletonClass Choices] (coins : Measure Coins)
    (select : Coins → Choices) (selected : Measurable select) (event : Choices → Set World)
    (risk : Coins → ENNReal) (conditional : ∀ coin, law (event (select coin)) ≤ risk coin) :
    (coins.prod law) {execution : Coins × World | execution.2 ∈ event (select execution.1)} ≤
      ∫⁻ coin, risk coin ∂coins := by
  let envelope : Set (Coins × World) := ⋃ choice : Choices,
    (select ⁻¹' {choice}) ×ˢ toMeasurable law (event choice)
  have measurable : MeasurableSet envelope := MeasurableSet.iUnion (fun choice =>
    (selected (measurableSet_singleton choice)).prod (measurableSet_toMeasurable _ _))
  have covered : {execution : Coins × World | execution.2 ∈ event (select execution.1)} ⊆ envelope := by
    intro execution occurred
    exact Set.mem_iUnion.mpr ⟨select execution.1,⟨rfl,subset_toMeasurable law _ occurred⟩⟩
  have section_eq (coin : Coins) : {world | (coin,world) ∈ envelope} = toMeasurable law (event (select coin)) := by
    ext world
    simp only [envelope,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_prod,Set.mem_preimage,Set.mem_singleton_iff]
    constructor
    · rintro ⟨choice,same,member⟩
      rwa [← same] at member
    · intro member
      exact ⟨select coin,rfl,member⟩
  apply (measure_mono covered).trans
  rw [Measure.prod_apply measurable]
  apply lintegral_mono
  intro coin
  change law {world | (coin,world) ∈ envelope} ≤ risk coin
  rw [section_eq,measure_toMeasurable]
  exact conditional coin

end
end FormalProof4FHE.HasteBoots.CountableCoinOuterBound
