module
public import FormalProof4FHE.HasteBoots.ScalarRoundChallengeMeaning
@[expose] public section

/-! A checked native scalar round can repair a false running claim only at
roots of its actual received polynomial's difference from the honest one.
The bound covers all successful native candidate prefixes on first exposure;
adaptive whole-verifier composition remains separate. -/
namespace FormalProof4FHE.HasteBoots.ScalarRoundHealingBound
open NativeFields (goldilocksModulus)
open NativeExtensionFields (Goldilocks3)
open NativeFieldWire (goldExtensionValue)
open NativeGoldExtensionArithmetic (Word)
open NativeScalarBatchWire (Statement Info Message RoundPacket)
open NativeScalarBatchPreflight (bindCheckedRound dimensions recurrence)
open NativeTranscript (Transcript)
open InputIndexedOracle (World law)
open OracleProgram (run)
open MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section

/-- Getter association with the actual bound packet supplies its passed
native recurrence, including every original equation in the batch. -/
theorem checked_message (transcript bound : Transcript) (packet : RoundPacket) (expected : List Word)
    (accepted : bindCheckedRound transcript packet expected = .ok bound) (index : ℕ) (message : Message) (prior : Word)
    (messageAt : packet.messages.val[index]? = some message) (priorAt : expected[index]? = some prior) :
    recurrence message prior = true := by
  have checked : NativeScalarBatchPreflight.check packet.messages.val expected = true := by
    unfold bindCheckedRound at accepted
    split at accepted
    next checked => exact checked
    next => contradiction
  have indexed : ∀ (i : ℕ) (messages : List Message) (claims : List Word),
      messages[i]? = some message → claims[i]? = some prior → (message,prior) ∈ messages.zip claims := by
    intro i
    induction i with
    | zero => intro messages claims first last; cases messages <;> cases claims <;> simp_all
    | succ i ih =>
      intro messages claims first last
      cases messages with
      | nil => cases first
      | cons head tail =>
        cases claims with
        | nil => cases last
        | cons value rest => exact List.mem_cons_of_mem _ (ih tail rest first last)
  exact (List.all_eq_true.mp checked) _ (indexed index packet.messages.val expected messageAt priorAt)

/-- The sent polynomial is constructed from received evaluations. Its
inequality follows from the native recurrence and false prior sum. -/
theorem message_distinct (statement : Statement) (admitted : dimensions statement = true)
    (info : Info) (member : info ∈ statement.infos.val) (message : Message)
    (width : message.evaluations.val.length = info.maxMultiplicands.val+1) (prior : Word)
    (checked : recurrence message prior = true) (honest : Polynomial Goldilocks3)
    (falsePrior : honest.eval 0+honest.eval 1 ≠ goldExtensionValue prior) :
    NativeGoldInterpolationPolynomial.polynomial info.maxMultiplicands.val message.evaluations.val width ≠ honest := by
  have recurrence := (NativeGoldInterpolationPolynomial.message_recurrence statement admitted info member message width prior).mp checked
  intro same
  rw [same] at recurrence
  exact falsePrior recurrence

/-- Actual successful scalar collection, raw decoding and interpolation heal
the chosen original equation. Suspensions and failures are not conditioned out. -/
def Event (transcript : Transcript) (packet : RoundPacket) (message : Message) (honest : Polynomial Goldilocks3) (world : World) : Prop :=
  ∃ (fuel : ℕ) (state : NativeFieldVector.State) (next : Transcript) (challenge updated : Word),
    (run (ScalarRoundChallengeMeaning.request fuel transcript packet) world).run.1 = .finished state next ∧
    NativeGoldLookupProducer.decode state.values = some challenge ∧
    NativeGoldInterpolation.interpolate message.evaluations.val challenge = some updated ∧
    goldExtensionValue updated = honest.eval (goldExtensionValue challenge)

/-- The native input already binds the whole received packet before its first
positive field read. One false equation suffices despite a shared challenge. -/
theorem event_bound {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (dummy : NativeRootMessage.Digest) (transcript bound : Transcript) (packet : RoundPacket) (expected : List Word)
    (accepted : bindCheckedRound transcript packet expected = .ok bound)
    (selected : CausalStreamExposure.firstRead step (past world).run = some (ScalarRoundChallengeMeaning.phase transcript packet).pending.input)
    (statement : Statement) (admitted : dimensions statement = true) (info : Info) (member : info ∈ statement.infos.val)
    (index : ℕ) (message : Message) (prior : Word)
    (messageAt : packet.messages.val[index]? = some message) (priorAt : expected[index]? = some prior)
    (width : message.evaluations.val.length = info.maxMultiplicands.val+1)
    (honest : Polynomial Goldilocks3) (honestDegree : honest.natDegree ≤ info.maxMultiplicands.val)
    (falsePrior : honest.eval 0+honest.eval 1 ≠ goldExtensionValue prior) :
    (law[|{other | (past other).run = (past world).run}]) {other | Event transcript packet message honest other} ≤
      (info.maxMultiplicands.val : ENNReal) / (goldilocksModulus^3 : ℕ) := by
  let sent := NativeGoldInterpolationPolynomial.polynomial info.maxMultiplicands.val message.evaluations.val width
  have checked := checked_message transcript bound packet expected accepted index message prior messageAt priorAt
  have different := message_distinct statement admitted info member message width prior checked honest falsePrior
  have sentDegree := (NativeGoldInterpolationPolynomial.message_value statement admitted info member message width NativeGoldLookup.zero).1
  apply le_trans (measure_mono ?_)
    (GoldScalarChallengeLaw.eventual_agreement_bound step replay world dummy (ScalarRoundChallengeMeaning.phase transcript packet)
      selected sent honest info.maxMultiplicands.val different sentDegree honestDegree)
  intro other event
  obtain ⟨fuel,state,next,challenge,updated,finished,decoded,interpolated,healed⟩ := event
  have value := ScalarRoundChallengeMeaning.finished_value fuel transcript packet other state next finished challenge decoded
  have polynomial := (NativeGoldInterpolationPolynomial.message_value statement admitted info member message width challenge).2
  rw [interpolated,Option.map_some] at polynomial
  refine ⟨fuel,?_⟩
  rw [value]
  exact (Option.some.inj polynomial).symm.trans healed

end
end FormalProof4FHE.HasteBoots.ScalarRoundHealingBound
