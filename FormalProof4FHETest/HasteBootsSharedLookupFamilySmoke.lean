module
import FormalProof4FHE.HasteBoots.RadixSharedSourceSlots
import Mathlib.Algebra.Field.ZMod
open FormalProof4FHE.HasteBoots
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim
open scoped Matrix
namespace HasteBootsSharedLookupFamilySmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
abbrev F := ZMod 17

-- Three radix limbs, two repetitions: request-major/repetition-minor jobs.
example : RadixSharedSourceSlots.slots (d := 3) (repetitions := 2) 2 = ![1,4,5] := rfl
example : RadixSharedSourceSlots.slots (d := 3) (repetitions := 2) 3 = ![1,4,5] := rfl
example : RadixSharedSourceSlots.slots (d := 3) (repetitions := 2) 5 2 = 6 := rfl
example (source : Fin 7) : ∃ job column,
    RadixSharedSourceSlots.slots (d := 3) (repetitions := 2) job column = source :=
  RadixSharedSourceSlots.coverage (d := 3) (repetitions := 2) (by decide +kernel) (by decide +kernel) source

def registry (index : Fin 8) : List NativeFieldRepresentation.GoldWord :=
  [⟨index.val,index.isLt.trans_le (by decide +kernel)⟩]

-- The omitted input is the only index shift. Digit/borrow order is literal.
example : NativeSharedLookupGuard.gather
    (List.ofFn (RadixLookupSources.comparisonRegistry (d := 3) registry)) [1,4,5] = some [[2],[5],[6]] := rfl
-- Alias slots retain both occurrences; source commitments are not duplicated.
example : NativeSharedLookupGuard.gather
    (List.ofFn (RadixLookupSources.comparisonRegistry (d := 3) registry)) [1,1,6] = some [[2],[2],[7]] := rfl

def geometry : SharedLookupOpeningFamily.Geometry 1 0 7 6 where
  front _ := 0
  suffix root := match root with | .inl _ => 0 | .inr _ => 1
  m _ := 2
  queries _ := 1
  sourceArity _ := rfl
  helperArity _ := rfl

-- The two repetitions do not become two original-source claims.
example (source : Fin 7) : (SharedLookupOpeningFamily.layout geometry (.inl source)).claims = 1 := rfl
example (job : Fin 6) : (SharedLookupOpeningFamily.layout geometry (.inr job)).claims = 2 := rfl

def claims (equation : Fin 6 × Bool) : Subclaim F 1 1 :=
  ⟨ScalarSumcheckQuery.query 1 ![3],fun _ => if equation.2 then 9 else 4⟩
theorem valid : SharedScalarBatchQuery.Valid (some (claims,())) :=
  ⟨fun _ => ScalarSumcheckQuery.scalar_query _,fun _ _ => rfl⟩
def sources (source : Fin 7) : Fin 2 → F := ![source.val+1,7]
def helpers (_ : Fin 6) : F := 12
def equalityPoints (_ : Fin 6) : Fin 1 → F := ![5]
def packet : SharedLookupOpeningFamily.Packet F F 2 7 1 6 :=
  SharedLookupOpeningFamily.ofBatch (d := 1) (padding := 1) (c := 1) (row := 0)
    claims (0,false) sources helpers equalityPoints

def basis : Module.Basis (Fin 1) F F := Module.Basis.singleton _ _
-- Source openings retain raw packed vectors, including the second lane;
-- helper slots retain [sumcheck expected, received helper] in that order.
example : SharedLookupOpeningFamily.values (padding := 1) basis geometry packet (.inl 1) (0 : Fin 1) = ![2,7] := rfl
example : SharedLookupOpeningFamily.values (padding := 1) basis geometry packet (.inr 2) (0 : Fin 2) = PaddedExtension.encode (padding := 1) basis 4 := rfl
example : SharedLookupOpeningFamily.values (padding := 1) basis geometry packet (.inr 2) (1 : Fin 2) = PaddedExtension.encode (padding := 1) basis 12 := rfl

-- Pulling the batch through the packet preserves the actual subclaims and
-- the job-local registry slice. It does not reconstruct an independent point.
example (job : Fin 6) :
    SharedLookupOpeningFamily.pairPacket (d := 1) (padding := 1) (c := 1) (row := 0)
      (RadixSharedSourceSlots.slots (d := 3) (repetitions := 2)) packet job =
      ⟨claims (job,false),equalityPoints job,claims (job,true),
        ⟨fun column => sources (RadixSharedSourceSlots.slots (d := 3) (repetitions := 2) job column),helpers job⟩⟩ :=
  SharedLookupOpeningFamily.pairPacket_ofBatch (d := 1) (padding := 1) (c := 1) (row := 0)
    (count := 7) (repetitions := 6) (columns := fun _ => 3)
    (RadixSharedSourceSlots.slots (d := 3) (repetitions := 2)) claims valid (0,false) sources helpers equalityPoints job
end
end HasteBootsSharedLookupFamilySmoke
