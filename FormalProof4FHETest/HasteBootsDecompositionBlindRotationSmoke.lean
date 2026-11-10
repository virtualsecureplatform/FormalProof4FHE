module
import FormalProof4FHE.HasteBoots.DecompositionBlindRotation
import FormalProof4FHE.HasteBoots.RadixWitness
import FormalProof4FHETest.HasteBootsPackedBlindRotationTraceSmoke
open FormalProof4FHE.HasteBoots
open HasteBootsAccumulatorTraceSmoke HasteBootsHadamardBlindRotationSmoke
open HasteBootsPackedAccumulatorTraceSmoke (rounds embed decompositionA decompositionB holds)
open HasteBootsPackedBlindRotationTraceSmoke (stages)
open scoped Matrix
namespace HasteBootsDecompositionBlindRotationSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

def address (index : Fin 4) : MatrixFold.Cube 2 × Fin 1 := ((FlatMatrixFold.index 2).symm index,0)
def source (round : Fin 3) (half : Bool) (cell : MatrixFold.Cube 2) (_lane : Fin 1) : ZMod 17 :=
  tables.difference (AccumulatorTrace.active rounds.shape round) half (FlatMatrixFold.index 2 cell)
def registries (round : Fin 3) (half : Bool) : DecompositionBlindRotation.Registry 17 3 2 1 :=
  RadixWitness.tables 17 4 3 (source round half)

theorem source_binding (round : Fin 3) (half : Bool) :
    DecompositionBlindRotation.project (log := 2) (registries round half) address DecompositionLinear.input =
      tables.difference (AccumulatorTrace.active rounds.shape round) half := by
  funext index
  simp only [DecompositionBlindRotation.project, registries, RadixWitness.tables_input, source, address, Equiv.apply_symm_apply]
theorem linear (round : Fin 3) (half : Bool) : DecompositionLinear.Relation (4 : ZMod 17) (registries round half) :=
  RadixWitness.tables_valid (by decide +kernel) (by decide +kernel) (source round half)
theorem lookup (round : Fin 3) (half : Bool) (index : Fin 4) :
    RadixCanonicity.LookupAt 17 4 (registries round half) (address index).1 (address index).2 :=
  RadixWitness.tables_lookup (by decide +kernel) (source round half) _ _

-- Bind the actual original registry digit column to the original NTT factor.
-- This is checked directly, rather than assumed to be a canonical digit.
theorem ntt_binding (round : Fin 3) : ∀ half source (level : Fin 1),
    BlindRotationNTT.transform 2 (2 : ZMod 17)
      (DecompositionBlindRotation.project (log := 2) (registries round source) address
        (DecompositionLinear.digit (Fin.castLE (show 1 ≤ 3 by decide +kernel) level))) =
      PBSHadamardBlindRotation.project (stages round).external ((stages round).externalAddress half)
        (.inl (PBSHadamardBlindRotation.digitIndex (source,level),false)) := by
  fin_cases round <;> decide +kernel

theorem multiplication : PackedBlindRotationTrace.AllHolds (c := 1) (lanes := 1) 2 2 rounds tables controls stages := by
  intro round
  have original := HasteBootsPackedBlindRotationTraceSmoke.multiplication round
  have derived := DecompositionBlindRotation.digits_transform_of_constraints
    (log := 2) (levels := 1) 2 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (registries round) (fun _ => address) (tables.difference (AccumulatorTrace.active rounds.shape round))
    (source_binding round) (linear round) (lookup round) (stages round).external (stages round).externalAddress (ntt_binding round)
  exact { original with digits := derived }

-- The complete reference trace now uses concrete decomposition constraints.
example : final = NativeBlindRotation.run 2 (List.ofFn controls) accumulator :=
  PackedBlindRotationTrace.output_eq_run (c := 1) (lanes := 1) (r := 2)
    2 primitive embed rounds tables accumulator final decompositionA decompositionB holds 2 controls stages multiplication
example (round : Fin 3) : tables.external (AccumulatorTrace.active rounds.shape round) =
    NativeBlindRotation.externalProduct 2 (controls round).1 (tables.difference (AccumulatorTrace.active rounds.shape round)) := by
  have original := HasteBootsPackedBlindRotationTraceSmoke.multiplication round
  exact DecompositionBlindRotation.external_of_constraints (log := 2) (levels := 1)
    2 primitive 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (registries round) (fun _ => address) (controls round).1
    (tables.difference (AccumulatorTrace.active rounds.shape round)) (tables.external (AccumulatorTrace.active rounds.shape round))
    (source_binding round) (linear round) (lookup round) (stages round).external (stages round).externalAddress
    original.externalRelation (ntt_binding round) original.keys original.externalResult

-- The highest canonical representative uses the third limb: 16 = 4^2.
def edgeRegistry : DecompositionBlindRotation.Registry 17 3 2 1 :=
  RadixWitness.tables 17 4 3 (fun _ _ => 16)
example : DecompositionBlindRotation.project (log := 2) edgeRegistry address
    (DecompositionLinear.digit (2 : Fin 3)) = fun _ => 1 := by
  have bound : DecompositionBlindRotation.project (log := 2) edgeRegistry address DecompositionLinear.input =
      (fun _ => 16 : NativeBlindRotation.Poly 17 4) := by
    funext index
    exact RadixWitness.tables_input (p := 17) (radix := 4) (d := 3) (n := 2) (b := 1)
      (fun _ _ => (16 : ZMod 17)) (address index).1 (address index).2
  have canonical := DecompositionBlindRotation.digit_of_constraints (log := 2) (levels := 3)
    2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (show 3 ≤ 3 by decide +kernel)
    edgeRegistry address (fun _ => 16) bound
    (RadixWitness.tables_valid (by decide +kernel) (by decide +kernel) (fun _ _ => (16 : ZMod 17)))
    (fun _ => RadixWitness.tables_lookup (by decide +kernel) (fun _ _ => (16 : ZMod 17)) _ _) (2 : Fin 3)
  exact canonical.trans (by decide +kernel)

-- 1 + 4^2 = 17 is zero in the field, but is not the canonical encoding of 0.
def noncanonical : DecompositionBlindRotation.Registry 17 3 2 1 := fun factor _ _ =>
  (![0,1,0,1,0,0,0,0] : Fin 8 → ZMod 17) factor
theorem noncanonical_linear : DecompositionLinear.Relation (4 : ZMod 17) noncanonical := by
  unfold DecompositionLinear.Relation
  decide +kernel
theorem noncanonical_source : DecompositionBlindRotation.project (log := 2) noncanonical address DecompositionLinear.input = 0 := by decide +kernel
theorem noncanonical_wrong : DecompositionBlindRotation.project (log := 2) noncanonical address
    (DecompositionLinear.digit (Fin.castLE (show 1 ≤ 3 by decide +kernel) (0 : Fin 1))) ≠ NativeBlindRotation.digit 2 (0 : Fin 1) 0 := by decide +kernel
example : ∃ index, ¬RadixCanonicity.LookupAt 17 4 noncanonical (address index).1 (address index).2 := by
  have coverage := DecompositionBlindRotation.wrong_digit_coverage (log := 2) (levels := 1)
    2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    noncanonical address 0 (0 : Fin 1) noncanonical_wrong
  rcases coverage with wrongSource | wrongLinear | wrongLookup
  · exact False.elim (wrongSource noncanonical_source)
  · exact False.elim (wrongLinear noncanonical_linear)
  · exact wrongLookup
end
end HasteBootsDecompositionBlindRotationSmoke
