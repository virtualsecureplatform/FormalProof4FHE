module
import all FormalProof4FHE.HasteBoots.ScalarCompletedChallenge
import all FormalProof4FHETest.HasteBootsScalarUnboundedSmoke

namespace FormalProof4FHE.HasteBoots.ScalarCompletedSmoke
open ScalarReplaySmoke (statement proof machine target)
open ScalarExecutionRecoverySmoke (before decoded domain)
open HasteBootsSamplerAncestrySmoke (child worldZero worldReject)
open InputIndexedOracle (World)
open MeasureTheory ProbabilityTheory
noncomputable section

def execution (fuel : ℕ) (world : World) := NativeScalarBatchVerifier.execute statement proof fuel machine world

def firstEntry := (execution 9 worldZero).1.completed[0]'(by decide +kernel)
def secondEntry := (execution 9 worldZero).1.completed[1]'(by decide +kernel)
theorem firstMember : firstEntry ∈ (execution 9 worldZero).1.completed := List.getElem_mem _
theorem secondMember : secondEntry ∈ (execution 9 worldZero).1.completed := List.getElem_mem _

/-- Every actual active and completed collector has an original reader prefix,
for arbitrary worlds and analysis budgets, including rejection-only worlds. -/
example (fuel : ℕ) (world : World) : ScalarCollectorTrace.Traced (execution fuel world).1 world :=
  ScalarCollectorTrace.initialized child statement proof fuel world

example : firstEntry.coefficients.values = [0,0,0] ∧ firstEntry.coefficients.remaining = 0 ∧
    firstEntry.coefficients.phase.consumed.length = 24 := by decide +kernel
example : secondEntry.coefficients.values = [0,0,0] ∧ secondEntry.packet.round.val = 1 := by decide +kernel

/-- Resetting the reader is analysis of the original stream, not a receipt-
digest inverse: the native completed state still retains all raw chunks. -/
example : (ScalarCollectorTrace.start firstEntry.coefficients).consumed = [] ∧
    firstEntry.coefficients.chunks.length = 3 := by decide +kernel

example : (GoldScalarChallengeLaw.values 2 (ScalarCollectorTrace.start firstEntry.coefficients) worldZero).isNone = true ∧
    (GoldScalarChallengeLaw.values 3 (ScalarCollectorTrace.start firstEntry.coefficients) worldZero).isSome = true := by decide +kernel

example (fuel : ℕ) (world : World) (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (execution fuel world).1.completed) :
    ∃ collected, GoldScalarChallengeLaw.values collected (ScalarCollectorTrace.start entry.coefficients) world =
      some (NativeFieldWire.goldExtensionValue entry.challenge) :=
  ScalarCompletedChallenge.value child statement proof fuel world entry member

/-- An original producing tick is derived for every retained record, with its
literal decode, interpolation update and original prior expected vector. -/
example (fuel : ℕ) (world : World) (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (execution fuel world).1.completed) :
    ∃ index < fuel, ScalarCompletedOrigin.Produced (execution index world).1 world entry :=
  ScalarCompletedOrigin.initialized child statement proof fuel world entry member

/-- The actual zero-world completions occur at producing indices three and
seven; receipt finalization does not create a further record. -/
example : (List.range 9).filter (fun index => decide ((execution (index + 1) worldZero).1.completed.length =
    (execution index worldZero).1.completed.length + 1)) = [3,7] := by decide +kernel

/-- Each reader first rejects the full-width 0xff candidate, then accepts
three zero candidates. Receipt queries use the same deterministic world. -/
def worldOneReject : World
  | .inl (_,offset) => if offset < 8 then 255 else 0
  | .inr _ => 0

def mixedEntry := (execution 11 worldOneReject).1.completed[0]'(by decide +kernel)
theorem mixedMember : mixedEntry ∈ (execution 11 worldOneReject).1.completed := List.getElem_mem _

example : mixedEntry.coefficients.chunks.length = 4 ∧ mixedEntry.coefficients.phase.consumed.length = 32 ∧
    mixedEntry.coefficients.values = [0,0,0] := by decide +kernel
example : (GoldScalarChallengeLaw.values 3 (ScalarCollectorTrace.start mixedEntry.coefficients) worldOneReject).isNone = true ∧
    (GoldScalarChallengeLaw.values 4 (ScalarCollectorTrace.start mixedEntry.coefficients) worldOneReject).isSome = true := by decide +kernel

example : ∃ collected, GoldScalarChallengeLaw.values collected (ScalarCollectorTrace.start mixedEntry.coefficients) worldOneReject =
    some (NativeFieldWire.goldExtensionValue mixedEntry.challenge) :=
  ScalarCompletedChallenge.value child statement proof 11 worldOneReject mixedEntry mixedMember

example : (execution 10 worldReject).1.completed = [] ∧ (execution 10 worldReject).2.length = 10 := by decide +kernel

/-- Native recurrence failure retains earlier completed records and creates
no fictitious completed second-round collector. -/
def badProof : NativeScalarBatchPreflight.Proof :=
  ⟨[⟨[HasteBootsScalarFinishAncestrySmoke.message,HasteBootsScalarFinishAncestrySmoke.badMessage],by decide⟩],by decide⟩
example : (NativeScalarBatchVerifier.execute statement badProof 12 (NativeScalarBatchVerifier.initial child statement badProof) worldZero).1.completed.length = 1 ∧
    (NativeScalarBatchVerifier.execute statement badProof 12 (NativeScalarBatchVerifier.initial child statement badProof) worldZero).2.length = 6 := by decide +kernel

/-- Actual completed input recovery and collector correspondence are derived
together; no separate recovery or sampled-value witness is assumed. -/
example (fuel : ℕ) (world : World) (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (execution fuel world).1.completed) :
    ∃ configuration : ScalarRecoveredReplay.Configuration,
      ScalarRecoveredReplay.recover entry.coefficients.phase.pending.input = some configuration ∧
      configuration.view.history.statement = statement ∧ configuration.view.packet = entry.packet ∧
      ∃ collected, GoldScalarChallengeLaw.values collected (configuration.phase child.profile) world =
        some (NativeFieldWire.goldExtensionValue entry.challenge) :=
  ScalarCompletedChallenge.recover_completed child (NativeScalarBatchWire.bindStatement child statement) before statement proof decoded rfl
    (by decide +kernel) domain fuel world entry member

example : ∃ collected, GoldScalarChallengeLaw.values collected (ScalarRecoverySmoke.recovered.phase child.profile) worldZero =
    some (NativeFieldWire.goldExtensionValue secondEntry.challenge) :=
  ScalarCompletedChallenge.recovered_value target ScalarRecoverySmoke.recovered ScalarRecoverySmoke.found child statement proof 9 worldZero
    (by decide +kernel) domain secondEntry secondMember (by decide +kernel)

/-- The all-budget event now follows from a literal completed native record.
Neither collector completion nor a stopped-prior equality is a premise. -/
example : ScalarRecoveredUnboundedLaw.event target ScalarRecoverySmoke.recovered child.profile
    (fun prior _ => prior.1 = secondEntry.priorExpected) worldZero := by
  obtain ⟨index,_,produced,transfer⟩ := ScalarCompletedChallenge.completed_witness target ScalarRecoverySmoke.recovered
    ScalarRecoverySmoke.found child (NativeScalarBatchWire.bindStatement child statement) before statement proof decoded rfl
    (by decide +kernel) domain 9 worldZero secondEntry secondMember (by decide +kernel)
    (fun prior _ => prior.1 = secondEntry.priorExpected)
  obtain ⟨field,next,active,finished,priorEq,decodedWord,updated⟩ := produced
  apply transfer
  exact priorEq.symm

/-- A literal completed second round supplies a root-agreement event for the
toy false-prior polynomial pair 0 and X, without an assumed sampled value. -/
example : ScalarRecoveredUnboundedLaw.event target ScalarRecoverySmoke.recovered child.profile
    (fun _ value => True ∧ (Polynomial.C (0 : NativeExtensionFields.Goldilocks3)).eval value = Polynomial.X.eval value) worldZero := by
  obtain ⟨index,_,_,transfer⟩ := ScalarCompletedChallenge.completed_witness target ScalarRecoverySmoke.recovered
    ScalarRecoverySmoke.found child (NativeScalarBatchWire.bindStatement child statement) before statement proof decoded rfl
    (by decide +kernel) domain 9 worldZero secondEntry secondMember (by decide +kernel)
    (fun _ value => True ∧ (Polynomial.C (0 : NativeExtensionFields.Goldilocks3)).eval value = Polynomial.X.eval value)
  apply transfer
  have raw : secondEntry.challenge = NativeGoldLookup.zero := by decide +kernel
  have zeroValue : NativeFieldWire.goldExtensionValue secondEntry.challenge = 0 := by rw [raw,NativeGoldLookup.zero_value]
  simp [zeroValue]

/-- The same completed-round event has the one-exposure cubic root bound. -/
example : (InputIndexedOracle.law[|{other | (ScalarHealingSmoke.past other).run = (ScalarHealingSmoke.past worldZero).run}])
    {other | ScalarRecoveredUnboundedLaw.event target ScalarRecoverySmoke.recovered child.profile
      (fun _ value => True ∧ (Polynomial.C (0 : NativeExtensionFields.Goldilocks3)).eval value = Polynomial.X.eval value) other} ≤
        (1 : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) := by
  have bound := ScalarRecoveredUnboundedLaw.agreement_bound ScalarHealingSmoke.replay ScalarReplaySmoke.step worldZero
    (fun _ => 0) child.profile target ScalarRecoverySmoke.recovered ScalarRecoverySmoke.found rfl
    (fun _ => True) (fun _ => Polynomial.C 0) (fun _ => Polynomial.X) 1
    (by intro state _ _ same; have coefficient := congrArg (fun poly : Polynomial NativeExtensionFields.Goldilocks3 => poly.coeff 1) same; simp at coefficient)
    (by intro state _ _; simp) (by intro state _ _; simp)
  simpa only [Nat.cast_one] using bound

end
end FormalProof4FHE.HasteBoots.ScalarCompletedSmoke
