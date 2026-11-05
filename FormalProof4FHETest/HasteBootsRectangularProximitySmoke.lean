module

import all FormalProof4FHE.HasteBoots.RectangularOpening
import all Mathlib.Algebra.Field.ZMod

open FormalProof4FHE.HasteBoots
open FormalProof4FHE.HasteBoots.ModuleCodeProximity
open Code ProbabilityTheory
open scoped ProbabilityTheory

namespace HasteBootsRectangularProximitySmoke
local instance : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
abbrev Scalar := ZMod 5
abbrev Symbol := Fin 4 → Scalar

def code : Submodule Scalar (Fin 2 → Symbol) where
  carrier := {value | value 0 = value 1}
  zero_mem' := rfl
  add_mem' := fun hu hv => congrArg₂ (·+·) hu hv
  smul_mem' := fun a _ hu => congrArg (a • ·) hu

theorem distance : Code.minDist (code : Set (Fin 2 → Symbol)) = 2 := by
  classical
  have witnesses : {d | ∃ u ∈ (code : Set (Fin 2 → Symbol)),
      ∃ v ∈ (code : Set (Fin 2 → Symbol)), u ≠ v ∧ hammingDist u v = d}.Nonempty := by
    refine ⟨2,0,code.zero_mem,(fun _ _ => 1),rfl, ?_, ?_⟩
    · intro equal
      have atZero := congrFun (congrFun equal 0) 0
      exact (by decide +kernel : (0 : Scalar) ≠ 1) atZero
    · decide +kernel
  have minimal := Nat.sInf_mem witnesses
  change ∃ u ∈ (code : Set (Fin 2 → Symbol)), ∃ v ∈ (code : Set (Fin 2 → Symbol)),
    u ≠ v ∧ hammingDist u v = Code.minDist (code : Set (Fin 2 → Symbol)) at minimal
  obtain ⟨u,hu,v,hv,different,dist⟩ := minimal
  change u 0 = u 1 at hu
  change v 0 = v 1 at hv
  have atZero : u 0 ≠ v 0 := by
    intro same
    apply different
    funext position
    fin_cases position
    · exact same
    · exact hu.symm.trans (same.trans hv)
  have atOne : u 1 ≠ v 1 := by simpa only [← hu,← hv] using atZero
  have exactDistance : hammingDist u v = 2 := by
    have allDifferent : ∀ position, u position ≠ v position := by
      intro position
      fin_cases position
      · exact atZero
      · exact atOne
    simp [hammingDist,allDifferent]
  exact dist.symm.trans exactDistance

def word : WordStack (A := Symbol) (Fin 1) (Fin 2) :=
  fun _ position _ => if position = 0 then 0 else 1

theorem far : 0 < Code.distFromCode (⋈|word) (code^⋈(Fin 1)) := by
  classical
  by_contra notFar
  obtain ⟨source,coded,close⟩ := (Code.closeToCode_iff_closeToCodeword_of_minDist
    (u := (⋈|word)) (C := (code^⋈(Fin 1))) (e := 0)).mp (by simpa using not_lt.mp notFar)
  have same : (⋈|word) = source := hammingDist_eq_zero.mp (Nat.le_zero.mp close)
  rw [← same] at coded
  have rowCoded := (Code.mem_moduleInterleavedCode_iff (F := Scalar) (A := Symbol)
    (κ := Fin 1) (ι := Fin 2) (MC := code) (v := (⋈|word))).mp coded 0
  change word 0 0 = word 0 1 at rowCoded
  have contradiction := congrFun rowCoded 0
  exact (by decide +kernel : (0 : Scalar) ≠ 1) contradiction

example : Pr{let matrix ← $ᵗ (Fin 3 → Fin 1 → Scalar)}[∀ lane,
    Code.distFromCode (Fintype.linearCombination Scalar (Matrix.of.symm word) (matrix lane))
      (code : Set (Fin 2 → Symbol)) ≤ 0] ≤ (2/5 : ENNReal)^3 := by
  classical
  let : Fintype (Submodule.span Scalar (Set.range word)) := Fintype.ofFinite _
  let : SampleableType (Submodule.span Scalar (Set.range word)) := SampleableType.ofFintype _
  let : Fintype (toSpan (F := Scalar) word).toAddMonoidHom.ker := Fintype.ofFinite _
  let : SampleableType (toSpan (F := Scalar) word).toAddMonoidHom.ker := SampleableType.ofFintype _
  have bound := rectangular_bound code word 0 3 (by decide) (by rw [distance]; decide) far
  simpa only [distance,ZMod.card,Nat.cast_ofNat,ENat.natCast_zero] using bound


def domain : Fin 2 ↪ Scalar :=
  ⟨fun position => (position.val : Scalar),by decide +kernel⟩

theorem block_distance : Code.minDist
    (BlockCode.code domain 1 4 : Set (Fin 2 → Symbol)) = 2 := by
  simpa only [Fintype.card_fin] using BlockCode.minDist domain 1 4 (by decide)

theorem row_not_coded : (fun position => word 0 position) ∉ BlockCode.code domain 1 4 := by
  intro coded
  have zero : (fun position => word 0 position) = 0 := Code.eq_of_lt_dist coded
    (BlockCode.code domain 1 4).zero_mem (by
      rw [Code.dist_eq_minDist,block_distance]
      decide +kernel)
  have contradiction := congrFun (congrFun zero 1) 0
  exact (by decide +kernel : (1 : Scalar) ≠ 0) contradiction

def layout : Fin 2 → Fin 1 → Fin 4 → Scalar := fun position row => word row position

theorem block_far : ¬ ∃ source, CommonSource.RowsIn (BlockCode.code domain 1 4) source ∧
    hammingDist layout source ≤ 0 := by
  rintro ⟨source,coded,close⟩
  have same : layout = source := hammingDist_eq_zero.mp (Nat.le_zero.mp close)
  rw [← same] at coded
  exact row_not_coded (coded 0)

/-- The semantic BlockCode bridge is inhabited at test width 3 and code width 4. -/
example : Pr{let matrix ← $ᵗ (Fin 3 → Fin 1 → Scalar)}[∀ lane,
    Code.distFromCode (StructuredOpening.combine (matrix lane) layout)
      (BlockCode.code domain 1 4 : Set (Fin 2 → Fin 4 → Scalar)) ≤ 0] ≤ (2/5 : ENNReal)^3 := by
  classical
  let : Fintype (Submodule.span Scalar (Set.range (RectangularBaseProximity.stack layout))) := Fintype.ofFinite _
  let : SampleableType (Submodule.span Scalar (Set.range (RectangularBaseProximity.stack layout))) :=
    SampleableType.ofFintype _
  let : Fintype (toSpan (F := Scalar) (RectangularBaseProximity.stack layout)).toAddMonoidHom.ker :=
    Fintype.ofFinite _
  let : SampleableType (toSpan (F := Scalar) (RectangularBaseProximity.stack layout)).toAddMonoidHom.ker :=
    SampleableType.ofFintype _
  have bound := RectangularBaseProximity.matrix_bound_distance domain 1 0 3 (by decide)
    layout (by decide) (by decide) block_far
  simpa only [Fintype.card_fin,ZMod.card,Nat.reduceSub,Nat.reduceAdd,Nat.cast_ofNat,ENat.natCast_zero] using bound


/-- Honest zero responses accept for every test matrix on the same columns. -/
example (matrix : Fin 3 → Fin 1 → Scalar) (draw : Fin 2 → Fin 2) :
    ∀ lane, ColumnOpening.Agrees
      (StructuredOpening.combine (matrix lane) (fun (_ : Fin 2) (_ : Fin 1) (_ : Fin 4) => (0 : Scalar)))
      (BlockEncoder.encode domain (fun _ : Fin 1 => fun _ : Fin 4 => (0 : Scalar))) draw := by
  intro lane position
  funext coordinate
  simp [StructuredOpening.combine,BlockEncoder.encode]

def repeatedRaw : Fin 2 → Fin 4 → Scalar := fun position _ => if position = 0 then 1 else 0

/-- Three identical response checks share one column draw: acceptance is 1/2,
not the product of three separate column acceptance probabilities. -/
example : Pr{let draw ← $ᵗ (Fin 1 → Fin 2)}[
    ∀ _lane : Fin 3, ColumnOpening.Agrees repeatedRaw (0 : Fin 2 → Fin 4 → Scalar) draw] =
    (1/2 : ENNReal) := by
  simp only [forall_const]
  have distance : hammingDist repeatedRaw (0 : Fin 2 → Fin 4 → Scalar) = 1 := by decide +kernel
  have probability := ColumnOpening.probability_eq repeatedRaw (0 : Fin 2 → Fin 4 → Scalar) 1
  simpa only [distance,Fintype.card_fin,Nat.reduceSub,Nat.cast_ofNat,Nat.cast_one,pow_one] using probability

end HasteBootsRectangularProximitySmoke

/-- info: 'FormalProof4FHE.HasteBoots.ModuleCodeProximity.direction_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ModuleCodeProximity.direction_eq

/-- info: 'FormalProof4FHE.HasteBoots.ModuleCodeProximity.directions_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ModuleCodeProximity.directions_eq

/-- info: 'FormalProof4FHE.HasteBoots.ModuleCodeProximity.many_close_scalars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ModuleCodeProximity.many_close_scalars

/-- info: 'FormalProof4FHE.HasteBoots.ModuleCodeProximity.few_close_scalars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ModuleCodeProximity.few_close_scalars

/-- info: 'FormalProof4FHE.HasteBoots.ModuleCodeProximity.common_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ModuleCodeProximity.common_support

/-- info: 'FormalProof4FHE.HasteBoots.ModuleCodeProximity.far_direction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ModuleCodeProximity.far_direction

/-- info: 'FormalProof4FHE.HasteBoots.ModuleCodeProximity.span_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ModuleCodeProximity.span_bound

/-- info: 'FormalProof4FHE.HasteBoots.ModuleCodeProximity.toSpan_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ModuleCodeProximity.toSpan_surjective

/-- info: 'FormalProof4FHE.HasteBoots.ModuleCodeProximity.coefficient_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ModuleCodeProximity.coefficient_bound

/-- info: 'FormalProof4FHE.HasteBoots.ModuleCodeProximity.uniform_repetition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ModuleCodeProximity.uniform_repetition

/-- info: 'FormalProof4FHE.HasteBoots.ModuleCodeProximity.rectangular_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ModuleCodeProximity.rectangular_bound

/-- info: 'FormalProof4FHE.HasteBoots.RectangularBaseProximity.combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularBaseProximity.combination

/-- info: 'FormalProof4FHE.HasteBoots.RectangularBaseProximity.far_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularBaseProximity.far_lift

/-- info: 'FormalProof4FHE.HasteBoots.RectangularBaseProximity.matrix_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularBaseProximity.matrix_bound

/-- info: 'FormalProof4FHE.HasteBoots.RectangularBaseProximity.matrix_bound_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularBaseProximity.matrix_bound_distance

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOpening.far_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOpening.far_bound

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOpening.encoded_far_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOpening.encoded_far_bound

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOpening.soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOpening.soundness_bound
