module
public import FormalProof4FHE.HasteBoots.PaddedPBSRequestComparisonStage
public import FormalProof4FHE.HasteBoots.RadixSharedSourceSlots
@[expose] public section

/-! Native canonical requests: one triple per digit, uniform configured
repetitions, literal modulus-digit transition tables and typed evaluation-vector
messages. The logical driver keeps all callback work; its polynomial meaning
is fixed here, so message degree bounds are derived rather than supplied. -/
namespace FormalProof4FHE.HasteBoots.KeySwitchPaddedComparisonConfig
open OracleSpec OracleComp BinaryTree
open scoped BigOperators
open MixedWidthSharedLookupPCSAlgebra
noncomputable section

/-- Native sum messages have two evaluations; identity messages have D+1. -/
def messageDegree (mode : Mode) (identity : Bool) : ℕ :=
  if identity then degree mode else 1

abbrev Message (K : Type) (jobs : ℕ) (mode : Mode) :=
  (equation : SharedLookupBatchSequence.Equation jobs) →
    Fin (messageDegree mode equation.2 + 1) → K

variable {q d padding c row digits repetitions active inactive : ℕ} [Fact q.Prime]
  {K Memory Cfg Input Digest SourceMemory HelperMemory : Type}
  [Field K] [Algebra (ZMod q) K] {mode : Mode}

/-- Replace only polynomial interpretation, retaining all prover callback work
and the literal received vectors. Native consecutive nodes fix that meaning. -/
def driver (p : ℕ) [CharP K p] (small : degree mode + 1 ≤ p)
    (raw : Driver (ZMod q) K (Message K (∑ _ : Fin digits, repetitions) mode)
      Memory Cfg Input Digest (d+padding) (2*digits+1) (∑ _ : Fin digits, repetitions) (c+row)) :
    Driver (ZMod q) K (Message K (∑ _ : Fin digits, repetitions) mode)
      Memory Cfg Input Digest (d+padding) (2*digits+1) (∑ _ : Fin digits, repetitions) (c+row) :=
  {raw with
    schedule := {raw.schedule with
      interpret := fun _ message equation =>
        NativePackedInterpolation.messagePolynomial
          (NativePackedInterpolation.consecutive p (by
            have bounded : messageDegree mode equation.2 + 1 ≤ degree mode + 1 := by
              cases mode <;> cases equation.2 <;>
                simp [messageDegree,degree,RepeatedLookupPCSAlgebra.degree]
            exact bounded.trans small))
          (message equation)}}

/-- Every native comparison source is used by a digit request, including the
last outgoing borrow. This is schedule coverage, not a source truth premise. -/
theorem coverage (positive : 0 < digits) (source : Fin (2*digits+1)) :
    ∃ limb column, RadixLookupSources.comparisonSlots limb column = source := by
  obtain ⟨job,column,same⟩ := RadixSharedSourceSlots.coverage positive (by decide : 0 < 1) source
  exact ⟨(finProdFinEquiv.symm job).1,column,same⟩

/-- Public dimensions, actual prover callbacks and multiplicities suffice to
construct the native request configuration. No message-degree law is an input. -/
def parameters (basis : Module.Basis (Fin d) (ZMod q) K) (shape : d+padding = 2^c)
    (positive : 0 < digits) (repeated : 0 < repetitions) (radix : ℕ)
    (logicalShape : active+inactive = 2^(c+row))
    (fullShape : mode = .full → active = 2^(c+row))
    (p : ℕ) [CharP K p] (small : degree mode + 1 ≤ p)
    (multiplicities : PaddedMixedWidthStagedSharedLookup.SourceEmission (2*digits+1) Digest SourceMemory →
      Fin digits → Fin (radix*2) → ZMod q)
    (raw : PaddedMixedWidthStagedSharedLookup.Emission (2*digits+1) (∑ _ : Fin digits, repetitions)
        Digest SourceMemory (RequestLookupPairMiddle.Memory K HelperMemory (fun _ : Fin digits => repetitions)) →
      Driver (ZMod q) K (Message K (∑ _ : Fin digits, repetitions) mode)
        Memory Cfg Input Digest (d+padding) (2*digits+1) (∑ _ : Fin digits, repetitions) (c+row)) :
    PaddedMixedWidthRequestSharedLookup.Parameters (ZMod q) K (Message K (∑ _ : Fin digits, repetitions) mode)
      Memory Cfg Input Digest SourceMemory HelperMemory d padding c row (2*digits+1) digits
      (fun _ => 3) (fun _ => radix*2) (fun _ => repetitions) mode where
  basis := basis
  shape := shape
  requestsPositive := positive
  repetitionsPositive := fun _ => repeated
  slots := RadixLookupSources.comparisonSlots
  coverage := coverage positive
  active := fun _ => active
  inactive := fun _ => inactive
  logicalShape := fun _ => logicalShape
  fullShape := fun full _ => fullShape full
  tables := fun limb => RadixLookupSources.publicTable q radix (RadixCanonicity.modulusDigit q radix limb.val)
  multiplicities := multiplicities
  driver := fun emission => driver p small (raw emission)
  sumDegree := by
    intro emission points message job
    exact NativePackedInterpolation.messagePolynomial_degree _ _
  identityDegree := by
    intro emission points message job
    exact NativePackedInterpolation.messagePolynomial_degree _ _

end
end FormalProof4FHE.HasteBoots.KeySwitchPaddedComparisonConfig
