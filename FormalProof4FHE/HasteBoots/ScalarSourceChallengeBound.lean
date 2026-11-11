module
public import FormalProof4FHE.HasteBoots.ScalarCompletedPrefix
public import FormalProof4FHE.HasteBoots.ScalarNativeSourceHealing
@[expose] public section

/-! Source-derived healing roots in the original all-budget causal event.
The polynomial families use fixed original factor tables and the native prior
point; no independent honest polynomial or sampled-value identity is supplied.
Fixing these tables at a protocol first exposure remains a caller obligation. -/
namespace FormalProof4FHE.HasteBoots.ScalarSourceChallengeBound
open InputIndexedOracle (Input World law)
open NativeTranscript (Transcript Execution)
open NativeRootMessage (Digest)
open NativeScalarBatchWire (Statement Info Message)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (CompletedRound)
open NativeGoldExtensionArithmetic (Word)
open NativeExtensionFields (Goldilocks3)
open NativeFieldWire (goldExtensionValue)
open MatrixFold (Cube)
open ScalarRecoveredUnboundedLaw (Prior)
open MeasureTheory ProbabilityTheory
noncomputable section
variable {Factor Term : Type} [Fintype Term]

/-- Total classification of the received vector. Invalid widths cannot be
used by a native healing witness; they are assigned the zero polynomial. -/
def received (info : Info) (message : Message) : Polynomial Goldilocks3 :=
  if width : message.evaluations.val.length = info.maxMultiplicands.val + 1 then
    NativeGoldInterpolationPolynomial.polynomial info.maxMultiplicands.val message.evaluations.val width
  else 0

theorem received_eq (info : Info) (message : Message)
    (width : message.evaluations.val.length = info.maxMultiplicands.val + 1) :
    received info message = NativeGoldInterpolationPolynomial.polynomial info.maxMultiplicands.val message.evaluations.val width := by
  simp only [received,dite_eq_left width]

def correct (arity : Term → ℕ) (coefficient : Term → Goldilocks3)
    (indices : (term : Term) → Fin (arity term) → Factor) (n : ℕ) (tables : Factor → Cube n → Goldilocks3)
    (prior : Prior) : Polynomial Goldilocks3 :=
  ScalarNativeSourceHealing.honest arity coefficient indices n tables prior.2.1

/-- Eligibility is a test of the already fixed native prior, not a condition
on the new challenge. Actual healing derives all three conjuncts. -/
def Eligible (info : Info) (message : Message) (arity : Term → ℕ) (coefficient : Term → Goldilocks3)
    (indices : (term : Term) → Fin (arity term) → Factor) (n : ℕ) (tables : Factor → Cube n → Goldilocks3)
    (prior : Prior) : Prop :=
  (received info message).natDegree ≤ info.maxMultiplicands.val ∧
    (correct arity coefficient indices n tables prior).natDegree ≤ info.maxMultiplicands.val ∧
    received info message ≠ correct arity coefficient indices n tables prior

def test (info : Info) (message : Message) (arity : Term → ℕ) (coefficient : Term → Goldilocks3)
    (indices : (term : Term) → Fin (arity term) → Factor) (n : ℕ) (tables : Factor → Cube n → Goldilocks3)
    (prior : Prior) (value : Goldilocks3) : Prop :=
  Eligible info message arity coefficient indices n tables prior ∧
    (received info message).eval value = (correct arity coefficient indices n tables prior).eval value

/-- One original causal scalar input pays D/p^3 for the union over every
auxiliary replay and native collector budget. The source tables are fixed
parameters of this first-exposure test. -/
theorem bound {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (step : S → OracleMachine.Command S A) (world : World) (dummy profile : Digest)
    (input : Input) (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover input = some configuration)
    (selected : CausalStreamExposure.firstRead step (past world).run = some input)
    (info : Info) (message : Message) (arity : Term → ℕ) (coefficient : Term → Goldilocks3)
    (indices : (term : Term) → Fin (arity term) → Factor) (n : ℕ) (tables : Factor → Cube n → Goldilocks3) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ScalarRecoveredUnboundedLaw.event input configuration profile
        (test info message arity coefficient indices n tables) other} ≤
          (info.maxMultiplicands.val : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) :=
  ScalarRecoveredUnboundedLaw.agreement_bound replay step world dummy profile input configuration found selected
    (Eligible info message arity coefficient indices n tables) (fun _ => received info message)
    (correct arity coefficient indices n tables) info.maxMultiplicands.val
    (fun _ _ eligible => eligible.2.2) (fun _ _ eligible => eligible.1) (fun _ _ eligible => eligible.2.1)

/-- An actual completed source healing supplies this same causal event. The
producing sampler's common point is derived from the native chain occurrence,
and collector completion is derived from the literal retained native record. -/
theorem completed_event (input : Input) (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover input = some configuration)
    (transcript result : Transcript) (frames : List TranscriptFrame.Frame) (statement : Statement) (proof : Proof)
    (decoded : TranscriptFrame.decodeAll transcript.input = some frames)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof) (first : Info)
    (head : statement.infos.val.head? = some first) (fuel : ℕ) (world : World)
    (before : List CompletedRound) (entry : CompletedRound) (after : List CompletedRound)
    (parts : (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed = before ++ entry :: after)
    (sameInput : entry.coefficients.phase.pending.input = input)
    (arity : Term → ℕ) (coefficient : Term → Goldilocks3)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Cube first.numVariables.val → Goldilocks3)
    (slot : ℕ) (info : Info) (message : Message) (prior next : Word)
    (infoAt : statement.infos.val[slot]? = some info) (messageAt : entry.packet.messages.val[slot]? = some message)
    (priorAt : entry.priorExpected[slot]? = some prior) (nextAt : entry.expected[slot]? = some next)
    (bounded : ∀ term, arity term ≤ info.maxMultiplicands.val)
    (healing : ScalarChainHealing.Healing (ScalarNativeSourceHealing.truth arity coefficient indices _ tables) slot before entry) :
    ScalarRecoveredUnboundedLaw.event input configuration transcript.profile
      (test info message arity coefficient indices _ tables) world := by
  have member : entry ∈ (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed := by rw [parts]; simp
  obtain ⟨index,indexBound,produced,transfer⟩ := ScalarCompletedChallenge.completed_witness input configuration found
    transcript result frames statement proof decoded accepted statementFits domain fuel world entry member sameInput
    (test info message arity coefficient indices _ tables)
  have point := ScalarCompletedPrefix.producing_point transcript result statement proof accepted fuel index
    (Nat.le_of_lt indexBound) world entry produced before after parts
  have preflight := (NativeScalarBatchPreflight.beginVerify_ok_iff transcript result statement proof).mp accepted
  have valid := NativeScalarBatchVerifierInvariant.execute_valid statement proof first preflight.1 preflight.2.1 head fuel
    _ world (NativeScalarBatchVerifierInvariant.initial_valid transcript result statement proof first accepted)
  have pending : before.length < first.numVariables.val := by
    have count := valid.2.2.2.1
    rw [parts,List.length_append,List.length_cons] at count
    have upper := valid.2.1
    omega
  have meaning := (NativeScalarBatchRoundMeaning.initialized_rounds transcript result statement proof accepted fuel world entry member).1
  obtain ⟨width,sentDegree,honestDegree,different,agreement⟩ := ScalarNativeSourceHealing.healing_root arity coefficient indices
    _ tables statement entry meaning before pending slot info message prior next infoAt messageAt priorAt nextAt bounded healing
  apply transfer
  simp only [test,Eligible,correct,ScalarPriorStability.prior,point,received_eq info message width]
  exact ⟨⟨sentDegree,honestDegree,different⟩,agreement⟩

/-- A fixed false original equation either remains false at the actual native
point or supplies one of the original completed inputs' causal source events.
Recovery, getter bounds, producer point, and polynomial witnesses are derived. -/
theorem false_or_event (transcript result : Transcript) (frames : List TranscriptFrame.Frame)
    (statement : Statement) (proof : Proof)
    (decoded : TranscriptFrame.decodeAll transcript.input = some frames)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof) (first : Info)
    (head : statement.infos.val.head? = some first) (fuel : ℕ) (world : World)
    (arity : Term → ℕ) (coefficient : Term → Goldilocks3)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Cube first.numVariables.val → Goldilocks3) (slot : ℕ) (info : Info)
    (infoAt : statement.infos.val[slot]? = some info)
    (bounded : ∀ term, arity term ≤ info.maxMultiplicands.val)
    (initial : ScalarChainHealing.value slot statement.claims.val ≠
      some (ScalarNativeSourceHealing.truth arity coefficient indices _ tables [])) :
    ScalarChainHealing.value slot (NativeScalarBatchVerifier.execute statement proof fuel
        (NativeScalarBatchVerifier.initial transcript statement proof) world).1.state.expected ≠
      some (ScalarNativeSourceHealing.truth arity coefficient indices _ tables
        ((NativeScalarBatchVerifier.execute statement proof fuel
          (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed.map (fun entry => entry.challenge))) ∨
    ∃ entry ∈ (NativeScalarBatchVerifier.execute statement proof fuel
        (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed,
      ∃ message, entry.packet.messages.val[slot]? = some message ∧
        ∃ configuration : ScalarRecoveredReplay.Configuration,
          ScalarRecoveredReplay.recover entry.coefficients.phase.pending.input = some configuration ∧
          ScalarRecoveredUnboundedLaw.event entry.coefficients.phase.pending.input configuration transcript.profile
            (test info message arity coefficient indices _ tables) world := by
  rcases ScalarNativeSourceHealing.initialized transcript result statement proof accepted fuel world
    arity coefficient indices _ tables slot initial with stillFalse | healed
  · exact Or.inl stillFalse
  · obtain ⟨before,entry,after,parts,healing⟩ := healed
    have member : entry ∈ (NativeScalarBatchVerifier.execute statement proof fuel
        (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed := by rw [parts]; simp
    have meaning := (NativeScalarBatchRoundMeaning.initialized_rounds transcript result statement proof accepted fuel world entry member).1
    obtain ⟨priorCount,nextCount,messageCount,infoCount,_⟩ := meaning
    have slotBound := (List.getElem?_eq_some_iff.mp infoAt).1
    have messageBound : slot < entry.packet.messages.val.length := by omega
    have priorBound : slot < entry.priorExpected.length := by omega
    have nextBound : slot < entry.expected.length := by omega
    let message := entry.packet.messages.val[slot]'messageBound
    let prior := entry.priorExpected[slot]'priorBound
    let next := entry.expected[slot]'nextBound
    have messageAt : entry.packet.messages.val[slot]? = some message := List.getElem?_eq_some_iff.mpr ⟨messageBound,rfl⟩
    have priorAt : entry.priorExpected[slot]? = some prior := List.getElem?_eq_some_iff.mpr ⟨priorBound,rfl⟩
    have nextAt : entry.expected[slot]? = some next := List.getElem?_eq_some_iff.mpr ⟨nextBound,rfl⟩
    obtain ⟨configuration,found,_,_,_⟩ := ScalarCompletedChallenge.recover_completed transcript result frames statement proof
      decoded accepted statementFits domain fuel world entry member
    refine Or.inr ⟨entry,member,message,messageAt,configuration,found,?_⟩
    exact completed_event _ configuration found transcript result frames statement proof decoded accepted statementFits domain first head
      fuel world before entry after parts rfl arity coefficient indices tables slot info message prior next
      infoAt messageAt priorAt nextAt bounded healing

end
end FormalProof4FHE.HasteBoots.ScalarSourceChallengeBound
