module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchRecoveredSourceAvailability
import all FormalProof4FHE.HasteBoots.NativeGoldBatchWitnessedColumnBound
import all FormalProof4FHETest.HasteBootsSelectedSourceSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World law)
open NativeTranscript (Observation)
open NativeGoldColumnAuthentication (encoding)
open NativeMerkleShapeFamily (shape)
open OracleProgram (run)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
namespace HasteBootsFirstFieldSourceSmoke
noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq
open HasteBootsBatchMeaningSmoke (root)

section Prefix
open HasteBootsFieldInputSmoke (view)
def key := NativeGoldBatchFirstFieldSource.input view
def before : List Observation := [.start key,.output key 70 [],.output [99] 4 [7],.hash [77] (List.ofFn root)]
def later : List Observation := before ++ [.output key 999 [0],.hash [78] (List.ofFn root)]
example : CausalFirstStreamPrefix.recover key before = none := by decide +kernel
example : CausalFirstStreamPrefix.recover key later = some before := by decide +kernel
example (suffix : List Observation) : CausalFirstStreamPrefix.recover key (later++suffix) = some before :=
  CausalFirstStreamPrefix.recover_append key later suffix before (by decide +kernel)
theorem recoveredPrefix : NativeGoldBatchFirstFieldSource.recover root later view = some (NativeGoldBatchSelectedSource.log root before view) :=
  NativeGoldBatchFirstFieldSource.recover_at root before [.hash [78] (List.ofFn root)] view 999 [0] (by decide +kernel) (by decide)
example (suffix : List Observation) : NativeGoldBatchFirstFieldSource.recover root (later++suffix) view =
    some (NativeGoldBatchSelectedSource.log root before view) :=
  NativeGoldBatchFirstFieldSource.recover_append root later suffix view _ recoveredPrefix
end Prefix

section Witnessed
open HasteBootsBatchOrderedSmoke (world)
open HasteBootsEarlyReceiptSmoke (view step columnInput)
open HasteBootsFieldColumnSmoke (past replay first parsed power raw)
open NativeGoldBatchFieldColumnLaw (collected event)
def sometimesClaim (state : NativeFieldVector.State) (test : Fin 2) (column : Fin (2^5)) : Bool :=
  if (state.values[0]?).getD 0 = 0 then raw state test column else HasteBootsFieldColumnSmoke.claimed state test column
-- This completed state is correct, so an unconditional distance premise fails.
example : (collected root 18 view world).1.remaining = 0 := by decide +kernel
theorem noWitness : ¬∃ test : Fin 2, 1 ≤ hammingDist (raw (collected root 18 view world).1 test) (sometimesClaim (collected root 18 view world).1 test) := by decide +kernel
example : ¬ event root 18 view 5 (NativeGoldBatchWitnessedColumnBound.checked 5 view.column.index.count.val raw sometimesClaim 1) world := by
  unfold event
  rw [NativeIndexFirstReadLaw.values_run 5 _ _ _ _ HasteBootsFieldColumnSmoke.valid power]
  simp only [Option.elim_some]
  intro checked
  exact noWitness checked.2.1
-- The bound applies without a claim that every completed state disagrees.
example : (law[|{other | (past other).run = (past world).run}])
    {other | ∃ fuel, event root fuel view 5 (NativeGoldBatchWitnessedColumnBound.checked 5 view.column.index.count.val raw sometimesClaim 1) other} ≤
      ColumnOpening.missBound (Fin (2^5)) view.column.index.count.val 1 :=
  NativeGoldBatchWitnessedColumnBound.eventual_bound replay root view columnInput parsed step world first 5 power raw sometimesClaim 1
example : event root 18 view 5 (NativeGoldBatchWitnessedColumnBound.checked 5 view.column.index.count.val raw HasteBootsFieldColumnSmoke.claimed 1) world := by
  unfold event
  rw [NativeIndexFirstReadLaw.values_run 5 _ _ _ _ HasteBootsFieldColumnSmoke.valid power]
  simp only [Option.elim_some]
  unfold NativeGoldBatchWitnessedColumnBound.checked ColumnOpening.Agrees
  decide +kernel
end Witnessed

section Accepted
open HasteBootsBatchMeaningSmoke (ctx world)
open HasteBootsNativeFinishingSmoke (work choose completion executed parent accepted)
def decodedOption := NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world)
theorem present : decodedOption.isSome = true := by decide +kernel
def decoded := decodedOption.get present
theorem parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded := (Option.some_get present).symm
-- The column history has a far-offset field read, then a later hash.
def prelude : OracleProgram.Program Unit := .read (NativeGoldBatchFirstFieldSource.input decoded.field) 999 1
  (fun _ => .hash [77] (fun _ => .pure ()))
def columnHistory := (run prelude world).run.2
theorem recovered : NativeGoldBatchFirstFieldSource.recover root columnHistory decoded.field = some [] := by decide +kernel
example (fuel : ℕ) : NativeGoldBatchFirstFieldSource.recover root
    (NativeGoldBatchFieldColumnLaw.extended (fun oracle => run prelude oracle) root fuel decoded world).run.2 decoded.field = some [] :=
  NativeGoldBatchFirstFieldSource.recover_after_collect _ root fuel decoded world root [] recovered

def suffix := (run (NativeGoldBatchPcsProgram.program ctx choose 6 ()) world).run.2
def history := columnHistory++suffix
theorem nativeAccepted : NativeGoldBatchAnySourceRisk.Accepted world history ctx choose 6 () work := by
  refine ⟨?_,completion,parent,executed,accepted,List.sublist_append_right _ _⟩
  exact ⟨HasteBootsFieldInputSmoke.parentFrames,by decide +kernel,HasteBootsRecoveredChallengeSmoke.parentValid,by decide +kernel⟩
theorem truthful : ObservationReplay.Agrees world history :=
  (ObservationReplay.agrees_append _ _ _).mpr ⟨(OracleProgram.run_replay prelude).truthful world,
    (OracleProgram.run_replay (NativeGoldBatchPcsProgram.program ctx choose 6 ())).truthful world⟩
example (safe : ¬CheckpointAvailability.Disagreement encoding root shape (NativeGoldBatchFamilyAvailability.reconstructed root history)) :
    NativeGoldBatchRecoveredSourceAvailability.Available root ctx world work history decoded.field [] :=
  NativeGoldBatchRecoveredSourceAvailability.accepted_column_history root ctx world work choose 6 () columnHistory suffix decoded parsed
    (by decide +kernel) [] recovered nativeAccepted truthful safe
end Accepted
end
end HasteBootsFirstFieldSourceSmoke
