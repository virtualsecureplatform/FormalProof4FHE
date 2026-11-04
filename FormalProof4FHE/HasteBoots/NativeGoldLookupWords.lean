module

public import FormalProof4FHE.HasteBoots.NativeGoldLookupProducer

@[expose] public section

/-! The computable raw-word producer window after accepted coefficient draws.
Its relation to the existing abstract sampler's producer is exact. This does
not itself implement retries. `NativeGoldLookupSampler` supplies the raw
retry machine and its exact abstract execution/refinement bridge. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldLookupWords

open NativeFieldRepresentation (GoldWord)
open NativeGoldExtensionArithmetic (Word)
open NativeGoldLookupProducer (Output)

def produce (width : ℕ) (rows : List (List GoldWord)) (y r : Word) : Option Output :=
  let powers := NativeGoldLookup.powerRun y width
  let table := rows.map (NativeGoldLookup.compress powers.1)
  if NativeGoldLookup.allowed table r then
    (NativeGoldLookup.reciprocals (NativeGoldLookup.denominators r table)).map
      (fun inverses => ⟨y,r,powers.1,powers.2,table,inverses⟩)
  else none

def fromDraws (width : ℕ) (rows : List (List GoldWord)) (first last : NativeFieldVector.State) : Option Output :=
  (NativeGoldLookupProducer.decode first.values).bind (fun y =>
    (NativeGoldLookupProducer.decode last.values).bind (fun r => produce width rows y r))

/-- Word production is the existing producer after its actual source-word
getter succeeds; it accepts no inverse vector, table or power certificate. -/
theorem produce_eq (width : ℕ) (rows : List (List GoldWord))
    (selection : NativeLookupChallenge.Machine NativeExtensionFields.Goldilocks3) (y r : Word)
    (sources : NativeGoldLookupProducer.sourceWords selection = some (y,r)) :
    NativeGoldLookupProducer.produce width rows selection = produce width rows y r := by
  simp only [NativeGoldLookupProducer.produce,sources,Option.bind_some,produce]

theorem fromDraws_eq (width : ℕ) (rows : List (List GoldWord)) (first last : NativeFieldVector.State)
    (y r : Word) (firstDecoded : NativeGoldLookupProducer.decode first.values = some y)
    (lastDecoded : NativeGoldLookupProducer.decode last.values = some r) :
    fromDraws width rows first last = produce width rows y r := by
  simp only [fromDraws,firstDecoded,lastDecoded,Option.bind_some]

theorem produce_spec (width : ℕ) (rows : List (List GoldWord)) (y r : Word) (output : Output)
    (success : produce width rows y r = some output) :
    output.y = y ∧ output.r = r ∧ output.powers = (NativeGoldLookup.powerRun y width).1 ∧
      output.nextPower = (NativeGoldLookup.powerRun y width).2 ∧
      output.table = rows.map (NativeGoldLookup.compress output.powers) ∧
      NativeGoldLookup.allowed output.table r = true ∧
      NativeGoldLookup.reciprocals (NativeGoldLookup.denominators r output.table) = some output.inverses := by
  unfold produce at success
  dsimp only at success
  split at success
  next allowed =>
    obtain ⟨inverses,computed,same⟩ := Option.map_eq_some_iff.mp success
    subst output
    exact ⟨rfl,rfl,rfl,rfl,rfl,allowed,computed⟩
  next rejected => contradiction

end FormalProof4FHE.HasteBoots.NativeGoldLookupWords
