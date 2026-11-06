module
import all FormalProof4FHE.HasteBoots.RectangularBatchOpeningKernel
import all FormalProof4FHE.HasteBoots.NativeFields
import all FormalProof4FHETest.HasteBootsRectangularProximitySmoke
open FormalProof4FHE.HasteBoots
open Matrix ProbabilityTheory OracleComp
open scoped BigOperators
namespace HasteBootsRectangularMatrixSmoke
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
abbrev F := ZMod 5

def domain : Fin 3 ↪ F := ⟨fun position => (position.val : F),by decide +kernel⟩
def coefficients (row : Unit × Fin 3) : Fin 1 → Fin 4 → F := fun _ component => (row.2.val+component.val+1 : ℕ)
def word : Fin 3 → (Unit × Fin 3) → Fin 4 → F := fun position row => BlockEncoder.encode domain (coefficients row) position
def table : Unit → Fin 2 → Fin 3 → F := fun _ right lane => (lane.val+right.val+1 : ℕ)

theorem coded : CommonSource.RowsIn (BlockCode.code domain 1 4) word := fun row => BlockEncoder.encode_mem_code domain (coefficients row)

-- Decoded rows can have nonzero padding, which the original message excludes.
example : coefficients ((),0) 0 2 = 3 ∧ coefficients ((),0) 0 3 = 4 := by decide +kernel

theorem extracted : RectangularMatrixResponse.extractTable domain (by decide : 2 ≤ 1*4) word = table := by
  funext left right lane
  simp only [RectangularMatrixResponse.extractTable,word,ResponseCoefficients.decode_encode domain (by decide : 1 ≤ Fintype.card (Fin 3))]
  fin_cases right <;> rfl

def left : Unit → Matrix (Fin 3) (Fin 3) F := fun _ => !![1,1,0; 0,1,0; 0,0,1]
def right : Fin 2 → Matrix (Fin 3) (Fin 3) F := fun _ => !![1,0,0; 1,1,0; 0,0,1]
example : right 0 * left () ≠ left () * right 0 := by decide +kernel

example : RectangularMatrixResponse.finishEncoded domain (by decide : 2 ≤ 1*4) right
    (fun lane => StructuredOpening.combine (RectangularMatrixResponse.weights left lane) word) =
      matrixEvaluation left right table := by
  rw [RectangularMatrixResponse.finish_structured_eq_evaluation domain (by decide) (by decide) left right word coded,extracted]

example (messages : Fin 3 → Fin 2 → F) :
    RectangularMatrixResponse.finishEncoded domain (by decide : 2 ≤ 1*4) right
      (fun lane => BlockEncoder.encode domain (RowLayout.padded (m := 1) (b := 4) (messages lane))) =
    RectangularMatrixResponse.finishMessage right messages :=
  RectangularMatrixResponse.finishEncoded_padded domain (by decide) (by decide) right messages

-- The same algebra is inhabited at the BabyBear profile's independent widths.
def babyDomain : Fin 3 ↪ NativeFields.BabyBear := ⟨fun position => (position.val : NativeFields.BabyBear),by decide +kernel⟩
example (right : Fin 3 → Matrix (Fin 6) (Fin 6) NativeFields.BabyBear) (messages : Fin 6 → Fin 3 → NativeFields.BabyBear) :
    RectangularMatrixResponse.finishEncoded babyDomain (by decide : 3 ≤ 1*8) right
      (fun lane => BlockEncoder.encode babyDomain (RowLayout.padded (m := 1) (b := 8) (messages lane))) =
    RectangularMatrixResponse.finishMessage right messages :=
  RectangularMatrixResponse.finishEncoded_padded babyDomain (by decide) (by decide) right messages

example (table : Unit → Fin 2 → Fin 3 → F) :
    RectangularMatrixOpeningKernel.extract domain (by decide : 2 ≤ 1*4) 0
      (fun pos row => BlockEncoder.encode domain (RowLayout.padded (m := 1) (b := 4) (fun right => table row.1 right row.2)) pos) = table :=
  RectangularMatrixOpeningKernel.extract_encoded domain (by decide) (by decide) table

namespace Adaptive
open HasteBootsRectangularProximitySmoke (layout block_far block_distance)
abbrev Coins := Fin 3 → Fin 1 → F
abbrev Response := Fin 2 × Coins

def respond (matrix : Coins) : ProbComp Response := do
  let coin ← $ᵗ (Fin 2)
  pure (coin,matrix)

def claimed (_ : Coins) (response : Response) (_ : Fin 3) :=
  BlockEncoder.encode HasteBootsRectangularProximitySmoke.domain (fun _ : Fin 1 => fun _ : Fin 4 => (response.1.val : F))

example : Pr{let pair ← RectangularOpeningKernel.experiment (F := F) (Row := Fin 1) (Position := Fin 2) 3 2 respond}[
    ∀ lane, ColumnOpening.Agrees (StructuredOpening.combine (pair.1.1 lane) layout) (claimed pair.1.1 pair.1.2 lane) pair.2] ≤
      (2/5 : ENNReal)^3 + (1/2 : ENNReal)^2 := by
  classical
  let : Fintype (Submodule.span F (Set.range (RectangularBaseProximity.stack layout))) := Fintype.ofFinite _
  let : SampleableType (Submodule.span F (Set.range (RectangularBaseProximity.stack layout))) := SampleableType.ofFintype _
  let : Fintype (ModuleCodeProximity.toSpan (F := F) (RectangularBaseProximity.stack layout)).toAddMonoidHom.ker := Fintype.ofFinite _
  let : SampleableType (ModuleCodeProximity.toSpan (F := F) (RectangularBaseProximity.stack layout)).toAddMonoidHom.ker := SampleableType.ofFintype _
  have bound := RectangularOpeningKernel.far_bound HasteBootsRectangularProximitySmoke.domain 1 0 3 2 layout respond claimed
    (by decide) (by rw [block_distance]; decide) block_far
    (fun matrix response lane => BlockEncoder.encode_mem_code _ _)
  simpa only [block_distance,ZMod.card,ColumnOpening.missBound,Fintype.card_fin,Nat.reduceAdd,Nat.reduceSub,Nat.cast_ofNat,Nat.cast_one] using bound
end Adaptive

-- Probabilistic responses retain private coins and the earlier test matrix.
abbrev MatrixCoins := Fin 3 → (Unit × Fin 3) → F
abbrev MatrixResponseState := Fin 2 × MatrixCoins
def respond (matrix : MatrixCoins) : ProbComp MatrixResponseState := do
  let coin ← $ᵗ (Fin 2)
  pure (coin,matrix)
def testMessage (matrix : MatrixCoins) (response : MatrixResponseState) (lane : Fin 3) (r : Fin 2) : F :=
  matrix lane ((),0) + (response.1.val+r.val : ℕ)
def structuredMessage (matrix : MatrixCoins) (response : MatrixResponseState) (lane : Fin 3) (r : Fin 2) : F :=
  matrix lane ((),1) + (response.1.val+lane.val+r.val : ℕ)

example : Pr{let pair ← RectangularOpeningKernel.experiment (F := F) (Row := Unit × Fin 3) (Position := Fin 3) 3 2 respond}[
    RectangularMatrixResponse.finishMessage right (structuredMessage pair.1.1 pair.1.2) ≠
      matrixEvaluation left right (RectangularMatrixOpeningKernel.extract domain (by decide : 2 ≤ 1*4) 0 word) ∧
    RectangularMatrixOpeningKernel.Checks (m := 1) domain word pair.1.1 (testMessage pair.1.1 pair.1.2) pair.2 ∧
    RectangularMatrixOpeningKernel.Checks (m := 1) domain word (RectangularMatrixResponse.weights left) (structuredMessage pair.1.1 pair.1.2) pair.2] ≤
      (3/5 : ENNReal)^3 + max (ColumnOpening.missBound (Fin 3) 2 3) (ColumnOpening.missBound (Fin 3) 2 1) := by
  classical
  let : Fintype (Submodule.span F (Set.range (RectangularBaseProximity.stack word))) := Fintype.ofFinite _
  let : SampleableType (Submodule.span F (Set.range (RectangularBaseProximity.stack word))) := SampleableType.ofFintype _
  let : Fintype (ModuleCodeProximity.toSpan (F := F) (RectangularBaseProximity.stack word)).toAddMonoidHom.ker := Fintype.ofFinite _
  let : SampleableType (ModuleCodeProximity.toSpan (F := F) (RectangularBaseProximity.stack word)).toAddMonoidHom.ker := SampleableType.ofFintype _
  have distance : Code.minDist (BlockCode.code domain 1 4 : Set (Fin 3 → Fin 4 → F)) = 3 := by
    simpa only [Fintype.card_fin] using BlockCode.minDist domain 1 4 (by decide)
  have bound := RectangularMatrixOpeningKernel.soundness_bound domain (by decide : 1 ≤ Fintype.card (Fin 3))
    (by decide : 2 ≤ 1*4) 0 3 2 word left right respond testMessage structuredMessage (by decide) (by rw [distance]; decide)
  simpa only [distance,ZMod.card,Nat.cast_ofNat,Nat.sub_zero,Nat.reduceAdd] using bound
namespace Batch
def groupOf : Fin 3 → Fin 2 := ![0,0,1]
def groupLeft (group : Fin 2) : Unit → Matrix (Fin 3) (Fin 3) F := if group = 0 then left else fun _ => right 0
def queryRight (query : Fin 3) : Fin 2 → Matrix (Fin 3) (Fin 3) F := if query = 1 then fun _ => 1 else right

def honest (group : Fin 2) (lane : Fin 3) (r : Fin 2) : F := leftResponse (groupLeft group) table r lane
example : RectangularBatchOpeningKernel.finishMessage groupOf queryRight honest 0 ≠
    RectangularBatchOpeningKernel.finishMessage groupOf queryRight honest 1 := by decide +kernel

example (messages : Fin 2 → Fin 3 → Fin 2 → F) :
    RectangularBatchOpeningKernel.finishEncoded domain (by decide : 2 ≤ 1*4) groupOf queryRight
      (fun test => BlockEncoder.encode domain (RowLayout.padded (m := 1) (b := 4) (messages test.1 test.2))) =
    RectangularBatchOpeningKernel.finishMessage groupOf queryRight messages :=
  RectangularBatchOpeningKernel.finishEncoded_padded domain (by decide) (by decide) groupOf queryRight messages

def messages (matrix : MatrixCoins) (response : MatrixResponseState) (group : Fin 2) (lane : Fin 3) (r : Fin 2) : F :=
  structuredMessage matrix response lane r + (group.val : F)

example : Pr{let pair ← RectangularOpeningKernel.experiment (F := F) (Row := Unit × Fin 3) (Position := Fin 3) 3 2 respond}[
    (∃ query : Fin 3, RectangularBatchOpeningKernel.finishMessage groupOf queryRight (messages pair.1.1 pair.1.2) query ≠
      matrixEvaluation (groupLeft (groupOf query)) (queryRight query) (RectangularMatrixOpeningKernel.extract domain (by decide : 2 ≤ 1*4) 0 word)) ∧
    RectangularMatrixOpeningKernel.Checks (m := 1) domain word pair.1.1 (testMessage pair.1.1 pair.1.2) pair.2 ∧
    ∀ test : Fin 2 × Fin 3, ColumnOpening.Agrees
      (StructuredOpening.combine (RectangularBatchOpeningKernel.weights groupLeft test) word)
      (BlockEncoder.encode domain (RowLayout.padded (m := 1) (b := 4) (messages pair.1.1 pair.1.2 test.1 test.2))) pair.2] ≤
      (3/5 : ENNReal)^3 + max (ColumnOpening.missBound (Fin 3) 2 3) (ColumnOpening.missBound (Fin 3) 2 1) := by
  classical
  let : Fintype (Submodule.span F (Set.range (RectangularBaseProximity.stack word))) := Fintype.ofFinite _
  let : SampleableType (Submodule.span F (Set.range (RectangularBaseProximity.stack word))) := SampleableType.ofFintype _
  let : Fintype (ModuleCodeProximity.toSpan (F := F) (RectangularBaseProximity.stack word)).toAddMonoidHom.ker := Fintype.ofFinite _
  let : SampleableType (ModuleCodeProximity.toSpan (F := F) (RectangularBaseProximity.stack word)).toAddMonoidHom.ker := SampleableType.ofFintype _
  have distance : Code.minDist (BlockCode.code domain 1 4 : Set (Fin 3 → Fin 4 → F)) = 3 := by
    simpa only [Fintype.card_fin] using BlockCode.minDist domain 1 4 (by decide)
  have bound := RectangularBatchOpeningKernel.soundness_bound domain (by decide : 1 ≤ Fintype.card (Fin 3))
    (by decide : 2 ≤ 1*4) 0 3 2 word groupOf groupLeft queryRight respond testMessage messages (by decide) (by rw [distance]; decide)
  simpa only [distance,ZMod.card,Nat.cast_ofNat,Nat.sub_zero,Nat.reduceAdd] using bound
end Batch

end
end HasteBootsRectangularMatrixSmoke
