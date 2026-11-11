module
import all FormalProof4FHE.HasteBoots.SharedNativeOpeningLifetime
import all FormalProof4FHE.HasteBoots.HelperOpeningLifetimeWitness
import all FormalProof4FHETest.HasteBootsSingleSelectedSmoke
import all FormalProof4FHETest.HasteBootsSingleLifetimeSmoke
import all Init.Data.String.Defs

namespace FormalProof4FHE.HasteBoots.SharedNativeLifetimeSmoke
noncomputable section
open InputIndexedOracle (World law)
open OracleProgram (Program run)
open MeasureTheory
open HasteBootsBatchMeaningSmoke (usize root)

def helper := SingleSelectedSmoke.ctx
/-- Reference parameter context; altered query data are not an accepted-call fixture. -/
def source : NativeGoldBatchPcsProgram.Context := {HasteBootsBatchMeaningSmoke.ctx with
  parameters := {HasteBootsBatchMeaningSmoke.ctx.parameters with width := usize 4}}

example : helper.parameters.width.val = 3 ∧ source.parameters.width.val = 4 ∧
    helper.parameters.code.blockWidth.val = 4 ∧ source.parameters.code.blockWidth.val = 4 := by decide +kernel
example : helper.parameters.code = source.parameters.code := rfl

/-- Equal code values cannot establish the full parameter association. -/
example : helper.parameters ≠ source.parameters := by
  intro same
  have width := congrArg (fun parameters => parameters.width.val) same
  have impossible : (3 : ℕ) = 4 := width
  cases impossible

example : SingleOpeningFieldMatrix.count helper = 18 ∧ NativeGoldBatchFieldMatrix.count source = 32 := by decide +kernel

/-- Distinct original constructor requests can produce identical retained code. -/
example : NativeGoldBlockCode.build helper.tables (usize 2) (usize 4) (usize 2) =
    NativeGoldBlockCode.build helper.tables (usize 2) (usize 4) (usize 4) := by decide +kernel
example : (⟨usize 2,usize 4,usize 2⟩ : NativeGoldBlockCodeProgram.Request) ≠ ⟨usize 2,usize 4,usize 4⟩ := by
  intro same
  have blowup := congrArg (fun request => request.blowup.val) same
  have impossible : (2 : ℕ) = 4 := blowup
  cases impossible

/-- One complete-program hash charge covers both independently packed roles. -/
example {S A : Type} (helperOrigin : CacheBackedSingleOpening.Origin helper) (sourceOrigin : CacheBackedCodeOrigin.Origin source)
    (prelude : Program S) (step : S → OracleMachine.Command S A) :
    law {world | SharedNativeOpeningLifetime.Failure ℕ (List InputIndexedOracle.Input) root helper source sourceOrigin 0 0
        (run prelude) id step world} ≤
      (⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge root (.pure prelude) (OracleMachinePrelude.prepend step) fuel) +
      (SingleOpeningLifetimeSoundness.exposureCharge (SingleOpeningLifetimeSoundness.clean prelude) id root helper helperOrigin 0 (OracleMachinePrelude.prepend step) +
        NativeGoldBatchLifetimeSoundness.exposureCharge (SingleOpeningLifetimeSoundness.clean prelude) id root source
          (sourceOrigin.primitiveAt source rfl) 0 (OracleMachinePrelude.prepend step)) :=
  SharedNativeOpeningLifetime.prelude_bound ℕ (List InputIndexedOracle.Input) root helper helperOrigin source sourceOrigin 0 0
    (by decide +kernel) (by decide +kernel) prelude step (by decide +kernel) (by decide +kernel)

def stopped (_ : Unit) : OracleMachine.Command Unit Unit := .done ()

theorem noWork (HelperMemory SourceMemory : Type) (sourceOrigin : CacheBackedCodeOrigin.Origin source) :
    {world | SharedNativeOpeningLifetime.Failure HelperMemory SourceMemory root helper source sourceOrigin 0 0
      (SingleOpeningLifetimeSoundness.clean ()) id stopped world} = ∅ := by
  ext world
  simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
  intro failed
  rcases failed with single | batch
  · obtain ⟨fuel,⟨witness⟩⟩ := single
    have touched := (SingleOpeningChallengeHistory.accepted_exposures witness.receipt _ witness.choose witness.verifierFuel witness.memory witness.accepted).1
    have never (input : InputIndexedOracle.Input) : CausalStreamExposure.seen
        (CausalExposureLifetime.history (SingleOpeningLifetimeSoundness.clean ()) id stopped fuel world).run.2 input = false := by
      cases fuel <;> rfl
    have impossible := (never _).symm.trans touched
    cases impossible
  · obtain ⟨fuel,⟨witness⟩⟩ := batch
    have touched := (NativeGoldBatchChallengeHistory.accepted_exposures witness.candidate world witness.work _ witness.choose witness.verifierFuel witness.memory witness.accepted).1
    have never (input : InputIndexedOracle.Input) : CausalStreamExposure.seen
        (CausalExposureLifetime.history (SingleOpeningLifetimeSoundness.clean ()) id stopped fuel world).run.2 input = false := by
      cases fuel <;> rfl
    have impossible := (never _).symm.trans touched
    cases impossible

/-- Neither kind of accepted-call witness can be created by an empty trace. -/
example (sourceOrigin : CacheBackedCodeOrigin.Origin source) :
    law {world | SharedNativeOpeningLifetime.Failure ℕ (List InputIndexedOracle.Input) root helper source sourceOrigin 0 0
      (SingleOpeningLifetimeSoundness.clean ()) id stopped world} = 0 := by
  rw [noWork]
  exact measure_empty

end
end FormalProof4FHE.HasteBoots.SharedNativeLifetimeSmoke
