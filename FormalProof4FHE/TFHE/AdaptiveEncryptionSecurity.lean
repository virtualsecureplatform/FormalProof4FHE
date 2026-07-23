/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.SubspaceLWE.Security
import FormalProof4FHE.TFHE.MultiQuerySecurity

/-!
# Query-Bounded Adaptive Native TFHE Encryption Security

This file strengthens the fixed-batch TFHE experiment to a sequential left-or-right encryption
oracle.  After seeing one circular cloud key, an adversary may choose each message pair from all
earlier ciphertexts and its internal randomness.  One hidden bit is reused for every query.

The experiment front-loads `queryCount` independent zero-message TLWE rows as an eager tape.  A
query consumes one row and translates its body by the selected encoded message.  The public query
bound proves that the fallback sampler is unobservable, giving the standard lazy-or-eager oracle
equivalence.  The resulting joint-LWE reduction contains every KSK row and exactly `queryCount`
input rows under the same scalar secret.

As in the one-time and fixed-batch theorems, the circular cloud-key replacement occurs once for
the whole continuation.  The remaining non-LWE term is still the explicit direct-bilinear
cross-key KDM premise; this module does not claim it follows from ordinary LWE/RLWE.
-/

open Matrix OracleComp OracleSpec

namespace FormalProof4FHE.TFHE.Encryption.Adaptive

/-- Internal uniform queries plus sequential left-or-right encryption queries. -/
abbrev Interface (Message Ciphertext : Type) :=
  unifSpec + ((Message × Message) →ₒ Ciphertext)

/-- An adaptive encryption adversary sees the cloud key and returns its guess after interacting
with the encryption oracle. -/
abbrev Adversary (Message CloudKey Ciphertext : Type) :=
  CloudKey → OracleComp (Interface Message Ciphertext) Bool

/-- Only encryption calls, not the adversary's internal uniform queries, consume the query
budget. -/
def isEncryptionQuery {Message Ciphertext : Type} :
    (Interface Message Ciphertext).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance instDecidablePredIsEncryptionQuery {Message Ciphertext : Type} :
    DecidablePred (isEncryptionQuery (Message := Message) (Ciphertext := Ciphertext))
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

/-- Public query-bound predicate for an adaptive adversary. -/
def IsQueryBound {Message CloudKey Ciphertext : Type}
    (adversary : Adversary Message CloudKey Ciphertext) (queryCount : ℕ) : Prop :=
  ∀ cloudKey, IsQueryBoundP (adversary cloudKey)
    (isEncryptionQuery (Message := Message) (Ciphertext := Ciphertext)) queryCount

/-! ### Closure under public ciphertext evaluation -/

/-- Implement an oracle returning publicly evaluated ciphertexts by making one query to the
underlying ciphertext oracle and applying the public evaluator.  Internal uniform queries are
forwarded unchanged. -/
def publicEvaluationImpl {Message Ciphertext Output : Type}
    (evaluate : Ciphertext → Output) :
    QueryImpl (Interface Message Output) (OracleComp (Interface Message Ciphertext)) := by
  intro query
  rcases query with uniformIndex | messages
  · exact liftM ((Interface Message Ciphertext).query (.inl uniformIndex))
  · exact do
      let ciphertext ← liftM ((Interface Message Ciphertext).query (.inr messages))
      return evaluate ciphertext

/-- Compile an adversary that receives publicly evaluated oracle responses into an adversary for
the underlying ciphertext oracle.  The evaluator may depend on the public cloud key already given
to both adversaries. -/
def compilePublicEvaluation {Message CloudKey Ciphertext Output : Type}
    (evaluate : CloudKey → Ciphertext → Output)
    (adversary : Adversary Message CloudKey Output) :
    Adversary Message CloudKey Ciphertext :=
  fun cloudKey ↦
    simulateQ (publicEvaluationImpl (evaluate cloudKey)) (adversary cloudKey)

/-- Public evaluation consumes exactly one underlying encryption query for every evaluated
encryption query and consumes none for internal uniform queries. -/
theorem compilePublicEvaluation_isQueryBound
    {Message CloudKey Ciphertext Output : Type}
    [IsUniformSpec (Interface Message Ciphertext)]
    (evaluate : CloudKey → Ciphertext → Output)
    (adversary : Adversary Message CloudKey Output) (queryCount : ℕ)
    (hbound : IsQueryBound adversary queryCount) :
    IsQueryBound (compilePublicEvaluation evaluate adversary) queryCount := by
  intro cloudKey
  apply IsQueryBoundP.simulateQ_of_step (hbound cloudKey)
  · intro query hcharged
    rcases query with uniformIndex | messages
    · simp [isEncryptionQuery] at hcharged
    · simp only [publicEvaluationImpl]
      change (¬ isEncryptionQuery (Message := Message) (Ciphertext := Ciphertext)
          (.inr messages) ∨ 0 < 1) ∧ ∀ _ : Ciphertext, True
      simp [isEncryptionQuery]
  · intro query hfree
    rcases query with uniformIndex | messages
    · simp only [publicEvaluationImpl]
      change (¬ isEncryptionQuery (Message := Message) (Ciphertext := Ciphertext)
          (.inl uniformIndex) ∨ 0 < 0) ∧ ∀ _, True
      simp [isEncryptionQuery]
    · simp [isEncryptionQuery] at hfree

section Native

variable {Message : Type}
  {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]

abbrev NativeAdversary (Message : Type)
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  Adversary Message
    (Encryption.NativeCloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (TLWE.Ciphertext (ZMod q) lweDimension)

/-- Translate adaptive encryption queries into one online LWE-source query each. -/
noncomputable def sourceReduction
    (bit : Bool) (encode : Message → ZMod q) :
    QueryImpl
      (Interface Message (TLWE.Ciphertext (ZMod q) lweDimension))
      (OracleComp
        (GeneralizedSubspaceLWE.Adaptive.SourceInterface (ZMod q) lweDimension)) := by
  intro query
  rcases query with uniformIndex | messages
  · exact liftM
      ((GeneralizedSubspaceLWE.Adaptive.SourceInterface
        (ZMod q) lweDimension).query (Sum.inl uniformIndex))
  · exact do
      let sample ← liftM
        ((GeneralizedSubspaceLWE.Adaptive.SourceInterface
          (ZMod q) lweDimension).query (Sum.inr ()))
      return ⟨sample.1,
        sample.2 + encode (if bit then messages.1 else messages.2)⟩

/-- The source reduction consumes at most one LWE sample per charged encryption query. -/
theorem sourceReduction_isQueryBoundP
    (bit : Bool) (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (cloudKey : Encryption.NativeCloudKey q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : IsQueryBoundP (adversary cloudKey)
      (isEncryptionQuery (Message := Message)
        (Ciphertext := TLWE.Ciphertext (ZMod q) lweDimension)) queryCount) :
    IsQueryBoundP
      (simulateQ (sourceReduction (lweDimension := lweDimension) bit encode)
        (adversary cloudKey))
      (GeneralizedSubspaceLWE.Adaptive.isSourceSample
        (F := ZMod q) (dimension := lweDimension)) queryCount := by
  letI : Inhabited (ZMod q) := ⟨0⟩
  letI : IsUniformSpec
      (Unit →ₒ GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension) :=
    IsUniformSpec.ofFintypeInhabited _
  apply IsQueryBoundP.simulateQ_of_step hbound
  · intro index hcharged
    rcases index with uniformIndex | messages
    · simp [isEncryptionQuery] at hcharged
    · simp only [sourceReduction]
      let sourceQuery : OracleComp
          (GeneralizedSubspaceLWE.Adaptive.SourceInterface (ZMod q) lweDimension)
          (GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension) :=
        liftM ((GeneralizedSubspaceLWE.Adaptive.SourceInterface
          (ZMod q) lweDimension).query (Sum.inr ()))
      let continuation := fun
          (sample : GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension) ↦
        (pure ⟨sample.1,
          sample.2 + encode (if bit then messages.1 else messages.2)⟩ :
            OracleComp
              (GeneralizedSubspaceLWE.Adaptive.SourceInterface (ZMod q) lweDimension)
              (TLWE.Ciphertext (ZMod q) lweDimension))
      change IsQueryBoundP (sourceQuery >>= continuation)
        (GeneralizedSubspaceLWE.Adaptive.isSourceSample
          (F := ZMod q) (dimension := lweDimension)) 1
      have hsource : IsQueryBoundP sourceQuery
          (GeneralizedSubspaceLWE.Adaptive.isSourceSample
            (F := ZMod q) (dimension := lweDimension)) 1 := by
        dsimp [sourceQuery]
        change (¬ GeneralizedSubspaceLWE.Adaptive.isSourceSample
            (F := ZMod q) (dimension := lweDimension) (Sum.inr ()) ∨ 0 < 1) ∧
          ∀ _ : GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension, True
        simp [GeneralizedSubspaceLWE.Adaptive.isSourceSample]
      have hcontinuation : ∀ sample ∈ support sourceQuery,
          IsQueryBoundP (continuation sample)
            (GeneralizedSubspaceLWE.Adaptive.isSourceSample
              (F := ZMod q) (dimension := lweDimension)) 0 := by
        simp [continuation]
      simpa [sourceQuery, continuation] using
        isQueryBoundP_bind (n := 1) (m := 0) hsource hcontinuation
  · intro index hfree
    rcases index with uniformIndex | messages
    · exact GeneralizedSubspaceLWE.Adaptive.isQueryBoundP_liftProbComp_left
        (F := ZMod q) (dimension := lweDimension)
        (liftM (unifSpec.query uniformIndex) : ProbComp (unifSpec.Range uniformIndex))
    · simp [isEncryptionQuery] at hfree

/-! ### Eager query tape and native games -/

/-- Execute an adaptive adversary from the ordered LWE rows encoded by a batch transcript. -/
noncomputable def runFromTranscript
    (bit : Bool) (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (cloudKey : Encryption.NativeCloudKey q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    {samples : ℕ}
    (transcript : FormalProof4FHE.LWE.BatchTranscript
      (ZMod q) lweDimension samples) : ProbComp Bool :=
  (simulateQ
      (GeneralizedSubspaceLWE.Adaptive.sourceImpl
        ($ᵗ GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension)).withPregen
      (simulateQ (sourceReduction (lweDimension := lweDimension) bit encode)
        (adversary cloudKey))).run'
    (GeneralizedSubspaceLWE.Adaptive.sourceSampleSeed
      (GeneralizedSubspaceLWE.Adaptive.batchSamples transcript))

/-- Query-bounded downstream experiment for already-generated native secrets and cloud key.  The
zero-message input randomness is sampled eagerly before the hidden bit; bounded adversaries cannot
observe the fallback source sampler. -/
noncomputable def continuation
    (queryCount : ℕ) (inputErrorSampler : ProbComp (ZMod q))
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) :=
  fun lweSecret _ bootstrapKey keySwitchKey ↦ do
    let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
      (embedBinarySecret lweSecret) 0
    let bit ← $ᵗ Bool
    let guess ← runFromTranscript bit encode adversary
      ⟨bootstrapKey, keySwitchKey⟩ tape
    return (bit == guess)

/-- Honest adaptive game with one native circular cloud key and at most `queryCount` encrypted
message-pair queries. -/
noncomputable def realGame
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ProbComp Bool :=
  Circular.realContinuationGame
    (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (continuation queryCount inputErrorSampler encode adversary)

/-- Adaptive hybrid with zero bootstrap messages and the real KSK messages. -/
noncomputable def bootstrapZeroGame
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ProbComp Bool :=
  Circular.bootstrapZeroContinuationGame
    (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (continuation queryCount inputErrorSampler encode adversary)

/-- The one-time cloud-key replacement cost for the entire adaptive oracle continuation. -/
noncomputable def bootstrapReplacementAdvantage
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ℝ :=
  (realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary).boolDistAdvantage
  (bootstrapZeroGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary)

/-- Honest adaptive advantage is bounded by one cloud-key replacement plus the zero-BRK
endpoint. -/
theorem abs_signedAdvantage_real_le_bootstrap_add_zero
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    |Encryption.signedAdvantage
      (realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      bootstrapReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        |Encryption.signedAdvantage
          (bootstrapZeroGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget encode adversary)| := by
  unfold Encryption.signedAdvantage bootstrapReplacementAdvantage
    ProbComp.boolDistAdvantage
  exact abs_sub_le
    (Pr[= true | realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget encode adversary]).toReal
    (Pr[= true | bootstrapZeroGame queryCount ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget encode adversary]).toReal
    (1 / 2 : ℝ)

/-- Shared-secret heterogeneous LWE problem for all KSK rows and the adaptive input tape. -/
abbrev jointLweProblem
    (q lweDimension keySwitchSamples queryCount : ℕ) [NeZero q]
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)) :=
  MultiQuery.jointLweProblem q lweDimension keySwitchSamples queryCount
    keySwitchErrorSampler inputErrorSampler

/-! ### Adaptive joint-LWE reduction -/

/-- Run the adaptive game from a supplied two-block transcript and zero-message BRK. -/
noncomputable def transcriptGame
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (bootstrapKey : Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
    (transcript : FormalProof4FHE.LWE.TwoBlock.Transcript (ZMod q) lweDimension
      (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels)
      queryCount) : ProbComp Bool := do
  let bit ← $ᵗ Bool
  let guess ← runFromTranscript bit encode adversary
    ⟨bootstrapKey, MultiQuery.keySwitchTranscript transcript⟩
    (MultiQuery.inputTranscript transcript)
  return (bit == guess)

/-- Joint-LWE distinguisher for an arbitrary ring-secret-dependent KSK message vector. -/
noncomputable def keySwitchMessageReduction
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (message : RingBinarySecret ringRank degree →
      Fin (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    LearningWithErrors.Adversary
      (jointLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
        keySwitchErrorSampler inputErrorSampler) :=
  fun transcript ↦ do
    let context ← Native.KeySwitchSecurity.zeroBootstrapContext
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
    transcriptGame encode adversary context.2
      (Encryption.Security.shiftFirstBlock (message context.1) transcript)

/-- Native zero-BRK game with arbitrary KSK messages and an adaptive query tape. -/
noncomputable def keySwitchMessageGame
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (message : RingBinarySecret ringRank degree →
      Fin (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ProbComp Bool := do
  let lweSecret ← Native.sampleLweSecret lweDimension
  let ringSecret ← Native.sampleRingSecret ringRank degree
  let bootstrapKey ← Native.generateZeroBootstrappingKey
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget ringSecret
  let switchKey ← TLWE.batchEncrypt lweDimension
    (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels)
    keySwitchErrorSampler (embedBinarySecret lweSecret) (message ringSecret)
  continuation queryCount inputErrorSampler encode adversary
    lweSecret ringSecret bootstrapKey switchKey

abbrev nativeKeySwitchMessage
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret ringRank degree) :
    Fin (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) → ZMod q :=
  Encryption.Security.nativeKeySwitchMessage keySwitchGadget ringSecret

/-- The bootstrap-zero adaptive endpoint is the native-message arbitrary KSK game. -/
theorem bootstrapZeroGame_eq_keySwitchMessageGame
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    bootstrapZeroGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary =
      keySwitchMessageGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary := by
  simp [bootstrapZeroGame, Circular.bootstrapZeroContinuationGame,
    Native.nativeCycleSpec, keySwitchMessageGame, nativeKeySwitchMessage,
    Encryption.Security.keySwitchSamples, Encryption.Security.nativeKeySwitchMessage,
    Native.generateKeySwitchKey]

omit [NeZero q] in
/-- Reading the second block is unaffected by a first-block KSK translation. -/
theorem inputTranscript_shiftFirstBlock_real
    {firstSamples : ℕ}
    (message : Fin firstSamples → ZMod q)
    (secret : Fin lweDimension → ZMod q)
    (firstChallenge : Matrix (Fin lweDimension) (Fin firstSamples) (ZMod q))
    (secondChallenge : Matrix (Fin lweDimension) (Fin queryCount) (ZMod q))
    (firstError : Fin firstSamples → ZMod q)
    (secondError : Fin queryCount → ZMod q) :
    MultiQuery.inputTranscript
        (Encryption.Security.shiftFirstBlock message
          ((firstChallenge, secondChallenge),
            (vecMul secret firstChallenge + firstError,
              vecMul secret secondChallenge + secondError))) =
      (secondChallenge, vecMul secret secondChallenge + secondError) := by
  rfl

omit [NeZero q] in
/-- Reading an unshifted real second block returns its matrix-form batch transcript. -/
theorem inputTranscript_real
    {firstSamples : ℕ}
    (secret : Fin lweDimension → ZMod q)
    (firstChallenge : Matrix (Fin lweDimension) (Fin firstSamples) (ZMod q))
    (secondChallenge : Matrix (Fin lweDimension) (Fin queryCount) (ZMod q))
    (firstError : Fin firstSamples → ZMod q)
    (secondError : Fin queryCount → ZMod q) :
    MultiQuery.inputTranscript
        ((firstChallenge, secondChallenge),
          (vecMul secret firstChallenge + firstError,
            vecMul secret secondChallenge + secondError)) =
      (secondChallenge, vecMul secret secondChallenge + secondError) := by
  rfl

/-- The arbitrary-message adaptive endpoint is exactly game 0 of its query-counted joint-LWE
reduction. -/
theorem keySwitchMessageGame_evalDist_eq_game0
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (message : RingBinarySecret ringRank degree →
      Fin (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    evalDist (keySwitchMessageGame queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget message encode adversary) =
      evalDist (LearningWithErrors.game0
        (jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget message encode adversary)) := by
  let samples := Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels
  let FirstChallenge := Matrix (Fin lweDimension) (Fin samples) (ZMod q)
  let SecondChallenge := Matrix (Fin lweDimension) (Fin queryCount) (ZMod q)
  let FirstError := Fin samples → ZMod q
  let SecondError := Fin queryCount → ZMod q
  let scalarSecrets := Native.sampleLweSecret lweDimension
  let contexts := Native.KeySwitchSecurity.zeroBootstrapContext
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
  let firstChallenges : ProbComp FirstChallenge := $ᵗ FirstChallenge
  let secondChallenges : ProbComp SecondChallenge := $ᵗ SecondChallenge
  let firstErrors : ProbComp FirstError :=
    ProbComp.sampleIID samples keySwitchErrorSampler
  let secondErrors : ProbComp SecondError :=
    ProbComp.sampleIID queryCount inputErrorSampler
  let finish := fun (lweSecret : BinarySecret lweDimension)
      (context : RingBinarySecret ringRank degree ×
        Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (challenge : FirstChallenge) (error : FirstError)
      (inputChallenge : SecondChallenge) (inputError : SecondError) ↦ do
    let bit ← $ᵗ Bool
    let guess ← runFromTranscript bit encode adversary
      ⟨context.2, TLWE.batchAssemble (embedBinarySecret lweSecret) challenge
        (message context.1) error⟩
      (TLWE.batchAssemble (embedBinarySecret lweSecret) inputChallenge 0 inputError)
    return (bit == guess)
  have native_eq :
      keySwitchMessageGame queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget message encode adversary =
        (scalarSecrets >>= fun lweSecret ↦
          contexts >>= fun context ↦
          firstChallenges >>= fun challenge ↦
          firstErrors >>= fun error ↦
          secondChallenges >>= fun inputChallenge ↦
          secondErrors >>= fun inputError ↦
          finish lweSecret context challenge error inputChallenge inputError) := by
    simp [keySwitchMessageGame, continuation, TLWE.batchEncrypt,
      scalarSecrets, contexts, Native.KeySwitchSecurity.zeroBootstrapContext,
      samples, Encryption.Security.keySwitchSamples,
      FirstChallenge, SecondChallenge, FirstError, SecondError,
      firstChallenges, secondChallenges, firstErrors, secondErrors, finish,
      bind_assoc, monad_norm]
  have lwe_eq :
      LearningWithErrors.game0
          (jointLweProblem q lweDimension samples queryCount
            keySwitchErrorSampler inputErrorSampler)
          (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget message encode adversary) =
        (firstChallenges >>= fun challenge ↦
          secondChallenges >>= fun inputChallenge ↦
          scalarSecrets >>= fun lweSecret ↦
          firstErrors >>= fun error ↦
          secondErrors >>= fun inputError ↦
          contexts >>= fun context ↦
          finish lweSecret context challenge error inputChallenge inputError) := by
    have uniformChallengeProduct :
        ($ᵗ (FormalProof4FHE.LWE.TwoBlock.Challenge
          (ZMod q) lweDimension samples queryCount) :
          ProbComp (FormalProof4FHE.LWE.TwoBlock.Challenge
            (ZMod q) lweDimension samples queryCount)) =
        Prod.mk <$> firstChallenges <*> secondChallenges := rfl
    rw [LearningWithErrors.game0]
    simp only [jointLweProblem, MultiQuery.jointLweProblem]
    unfold LearningWithErrors.distr
    simp only [FormalProof4FHE.LWE.TwoBlock.heterogeneousProblem]
    rw [uniformChallengeProduct]
    simp [keySwitchMessageReduction, transcriptGame,
      MultiQuery.keySwitchTranscript_shiftFirstBlock_real,
      inputTranscript_real,
      samples, Encryption.Security.keySwitchSamples,
      FirstChallenge, SecondChallenge, FirstError, SecondError,
      scalarSecrets, contexts, firstChallenges, secondChallenges,
      firstErrors, secondErrors, finish,
      bind_assoc, monad_norm]
  rw [native_eq, lwe_eq]
  exact Encryption.Security.evalDist_bind_six_reorder scalarSecrets contexts
    firstChallenges firstErrors secondChallenges secondErrors finish

/-! ### Uniform tapes and adaptive one-time padding -/

/-- View a matrix-form batch transcript as an indexed family of scalar LWE samples. -/
def batchSampleFunction
    {R : Type} {dimension samples : ℕ}
    (transcript : FormalProof4FHE.LWE.BatchTranscript R dimension samples) :
    Fin samples → ((Fin dimension → R) × R) :=
  fun sample ↦ (fun coordinate ↦ transcript.1 coordinate sample, transcript.2 sample)

/-- Matrix columns paired with output coordinates are a bijective presentation of a batch
transcript. -/
theorem batchSampleFunction_bijective
    {R : Type} (dimension samples : ℕ) :
    Function.Bijective
      (batchSampleFunction :
        FormalProof4FHE.LWE.BatchTranscript R dimension samples →
          Fin samples → ((Fin dimension → R) × R)) := by
  constructor
  · intro first second heq
    apply Prod.ext
    · funext coordinate sample
      exact congrArg (fun values ↦ (values sample).1 coordinate) heq
    · funext sample
      exact congrArg (fun values ↦ (values sample).2) heq
  · intro values
    exact ⟨(fun coordinate sample ↦ (values sample).1 coordinate,
      fun sample ↦ (values sample).2), rfl⟩

/-- A uniform matrix-form transcript is exactly an ordered list of independent uniform scalar
samples. -/
theorem evalDist_uniformBatch_batchSamples_eq_replicate
    (samples : ℕ) :
    evalDist
        (GeneralizedSubspaceLWE.Adaptive.batchSamples <$>
          ($ᵗ (FormalProof4FHE.LWE.BatchTranscript
            (ZMod q) lweDimension samples))) =
      evalDist
        (OracleComp.replicate samples
          ($ᵗ GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension)) := by
  let Sample := GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension
  let toFunction :
      FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension samples →
        Fin samples → Sample := batchSampleFunction
  let toList : (Fin samples → Sample) → List Sample := fun values ↦ List.ofFn values
  have hfunction :
      evalDist (toFunction <$>
          ($ᵗ (FormalProof4FHE.LWE.BatchTranscript
            (ZMod q) lweDimension samples))) =
        evalDist ($ᵗ (Fin samples → Sample)) :=
    evalDist_map_bijective_uniform_cross
      (α := FormalProof4FHE.LWE.BatchTranscript
        (ZMod q) lweDimension samples)
      (β := Fin samples → Sample) toFunction
      (batchSampleFunction_bijective lweDimension samples)
  have hiid := GeneralizedSubspaceLWE.Adaptive.evalDist_sampleIID_uniform
    (alpha := Sample) samples
  calc
    evalDist
        (GeneralizedSubspaceLWE.Adaptive.batchSamples <$>
          ($ᵗ (FormalProof4FHE.LWE.BatchTranscript
            (ZMod q) lweDimension samples))) =
      evalDist (toList <$> (toFunction <$>
        ($ᵗ (FormalProof4FHE.LWE.BatchTranscript
          (ZMod q) lweDimension samples)))) := by
        have hconvert :
            (GeneralizedSubspaceLWE.Adaptive.batchSamples :
              FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension samples →
                List Sample) =
              fun transcript ↦ toList (toFunction transcript) := by
          rfl
        rw [hconvert]
        simp [map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (toList <$> ($ᵗ (Fin samples → Sample))) := by
      exact evalDist_map_eq_of_evalDist_eq hfunction toList
    _ = evalDist (toList <$> ProbComp.sampleIID samples ($ᵗ Sample)) := by
      exact evalDist_map_eq_of_evalDist_eq hiid.symm toList
    _ = evalDist (OracleComp.replicate samples ($ᵗ Sample)) := by
      simp only [toList]
      rw [show ProbComp.sampleIID samples ($ᵗ Sample) =
          Fin.mOfFn samples (fun _ ↦ ($ᵗ Sample)) by rfl,
        GeneralizedSubspaceLWE.Adaptive.mOfFn_toList_eq_replicate]

/-- Installing a uniform batch transcript as the eager source tape is distributionally equal to
the online uniform source implementation for every bounded adaptive adversary. -/
theorem evalDist_uniformTranscript_runFromTranscript_eq_online
    (queryCount : ℕ) (bit : Bool) (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (cloudKey : Encryption.NativeCloudKey q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : IsQueryBoundP (adversary cloudKey)
      (isEncryptionQuery (Message := Message)
        (Ciphertext := TLWE.Ciphertext (ZMod q) lweDimension)) queryCount) :
    evalDist (do
        let transcript ←
          $ᵗ (FormalProof4FHE.LWE.BatchTranscript
            (ZMod q) lweDimension queryCount)
        runFromTranscript bit encode adversary cloudKey transcript) =
      evalDist
        (simulateQ
          (GeneralizedSubspaceLWE.Adaptive.sourceImpl
            ($ᵗ GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension))
          (simulateQ (sourceReduction (lweDimension := lweDimension) bit encode)
            (adversary cloudKey))) := by
  let Sample := GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension
  let sampleSampler : ProbComp Sample := $ᵗ Sample
  let computation :=
    simulateQ (sourceReduction (lweDimension := lweDimension) bit encode)
      (adversary cloudKey)
  let finish := fun (sourceSamples : List Sample) ↦
    (simulateQ
      (GeneralizedSubspaceLWE.Adaptive.sourceImpl sampleSampler).withPregen
      computation).run'
      (GeneralizedSubspaceLWE.Adaptive.sourceSampleSeed sourceSamples)
  have hsource : IsQueryBoundP computation
      (GeneralizedSubspaceLWE.Adaptive.isSourceSample
        (F := ZMod q) (dimension := lweDimension)) queryCount :=
    sourceReduction_isQueryBoundP bit encode adversary cloudKey hbound
  have hbatch := evalDist_uniformBatch_batchSamples_eq_replicate
    (q := q) (lweDimension := lweDimension) queryCount
  have hbatched := GeneralizedSubspaceLWE.Adaptive.evalDist_sourceImpl_eq_batched
    sampleSampler sampleSampler computation queryCount hsource
  calc
    evalDist (do
        let transcript ←
          $ᵗ (FormalProof4FHE.LWE.BatchTranscript
            (ZMod q) lweDimension queryCount)
        runFromTranscript bit encode adversary cloudKey transcript) =
      evalDist
        ((GeneralizedSubspaceLWE.Adaptive.batchSamples <$>
            ($ᵗ (FormalProof4FHE.LWE.BatchTranscript
              (ZMod q) lweDimension queryCount))) >>= finish) := by
          simp [runFromTranscript, Sample, sampleSampler, computation, finish,
            map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (OracleComp.replicate queryCount sampleSampler >>= finish) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hbatch finish
    _ = evalDist (simulateQ
          (GeneralizedSubspaceLWE.Adaptive.sourceImpl sampleSampler)
          computation) := hbatched.symm

/-- Convert a source sample into a shifted scalar ciphertext. -/
def shiftSample
    (offset : ZMod q)
    (sample : GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension) :
    TLWE.Ciphertext (ZMod q) lweDimension :=
  ⟨sample.1, sample.2 + offset⟩

/-- The unshifted carrier conversion from a source pair to a scalar ciphertext. -/
def sampleToCiphertext
    (sample : GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension) :
    TLWE.Ciphertext (ZMod q) lweDimension :=
  ⟨sample.1, sample.2⟩

/-- Translate only the body of a source pair. -/
def shiftSourceSample
    (offset : ZMod q)
    (sample : GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension) :
    GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension :=
  (sample.1, sample.2 + offset)

/-- Inverse source-pair body translation. -/
def unshiftSourceSample
    (offset : ZMod q)
    (sample : GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension) :
    GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension :=
  (sample.1, sample.2 - offset)

omit [NeZero q] in
@[simp]
theorem unshiftSourceSample_shiftSourceSample
    (offset : ZMod q)
    (sample : GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension) :
    unshiftSourceSample offset (shiftSourceSample offset sample) = sample := by
  rcases sample with ⟨mask, body⟩
  simp [unshiftSourceSample, shiftSourceSample]

omit [NeZero q] in
@[simp]
theorem shiftSourceSample_unshiftSourceSample
    (offset : ZMod q)
    (sample : GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension) :
    shiftSourceSample offset (unshiftSourceSample offset sample) = sample := by
  rcases sample with ⟨mask, body⟩
  simp [unshiftSourceSample, shiftSourceSample]

omit [NeZero q] in
theorem shiftSourceSample_bijective (offset : ZMod q) :
    Function.Bijective
      (shiftSourceSample (lweDimension := lweDimension) offset) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨unshiftSourceSample offset, ?_, ?_⟩
  · exact unshiftSourceSample_shiftSourceSample offset
  · exact shiftSourceSample_unshiftSourceSample offset

omit [NeZero q] in
theorem sampleToCiphertext_shiftSourceSample
    (offset : ZMod q)
    (sample : GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension) :
    sampleToCiphertext (shiftSourceSample offset sample) = shiftSample offset sample := by
  rfl

/-- Inverse of `shiftSample`. -/
def unshiftCiphertext
    (offset : ZMod q) (ciphertext : TLWE.Ciphertext (ZMod q) lweDimension) :
    GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension :=
  (ciphertext.mask, ciphertext.body - offset)

omit [NeZero q] in
@[simp]
theorem unshiftCiphertext_shiftSample
    (offset : ZMod q)
    (sample : GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension) :
    unshiftCiphertext offset (shiftSample offset sample) = sample := by
  rcases sample with ⟨mask, body⟩
  simp [unshiftCiphertext, shiftSample]

omit [NeZero q] in
@[simp]
theorem shiftSample_unshiftCiphertext
    (offset : ZMod q) (ciphertext : TLWE.Ciphertext (ZMod q) lweDimension) :
    shiftSample offset (unshiftCiphertext offset ciphertext) = ciphertext := by
  rcases ciphertext with ⟨mask, body⟩
  simp [unshiftCiphertext, shiftSample]

omit [NeZero q] in
theorem shiftSample_bijective (offset : ZMod q) :
    Function.Bijective
      (shiftSample (lweDimension := lweDimension) offset) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨unshiftCiphertext offset, ?_, ?_⟩
  · exact unshiftCiphertext_shiftSample offset
  · exact shiftSample_unshiftCiphertext offset

/-- Bit-independent online oracle returning a fresh uniform scalar ciphertext per query. -/
noncomputable def plainUniformImpl :
    QueryImpl (Interface Message (TLWE.Ciphertext (ZMod q) lweDimension)) ProbComp :=
  (QueryImpl.ofLift unifSpec ProbComp) +
    (fun (_ : Message × Message) ↦
      sampleToCiphertext <$>
        ($ᵗ GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension) :
      QueryImpl ((Message × Message) →ₒ TLWE.Ciphertext (ZMod q) lweDimension) ProbComp)

/-- Composing the uniform LWE source with message translation is pointwise equal in distribution
to the bit-independent uniform ciphertext oracle. -/
theorem evalDist_uniformSource_compose_sourceReduction
    (bit : Bool) (encode : Message → ZMod q)
    (query : (Interface Message (TLWE.Ciphertext (ZMod q) lweDimension)).Domain) :
    evalDist
        ((GeneralizedSubspaceLWE.Adaptive.sourceImpl
          ($ᵗ GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension) ∘ₛ
          sourceReduction (lweDimension := lweDimension) bit encode) query) =
      evalDist (plainUniformImpl (Message := Message)
        (q := q) (lweDimension := lweDimension) query) := by
  rcases query with uniformIndex | messages
  · simp [QueryImpl.apply_compose, sourceReduction,
      GeneralizedSubspaceLWE.Adaptive.sourceImpl, plainUniformImpl]
    intro response
    change Pr[= response | (QueryImpl.id' unifSpec) uniformIndex] = _
    simp
  · let offset := encode (if bit then messages.1 else messages.2)
    let sampleSampler : ProbComp
        (GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension) :=
      $ᵗ GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension
    have hsource :
        GeneralizedSubspaceLWE.Adaptive.sourceImpl sampleSampler (Sum.inr ()) =
          sampleSampler := by
      rfl
    have hshift :
        evalDist (shiftSourceSample offset <$>
            ($ᵗ GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension)) =
          evalDist
            ($ᵗ GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension) :=
      evalDist_map_bijective_uniform_cross
        (α := GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension)
        (β := GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension)
        (shiftSourceSample offset) (shiftSourceSample_bijective offset)
    have hmapped := evalDist_map_eq_of_evalDist_eq hshift sampleToCiphertext
    simpa [QueryImpl.apply_compose, sourceReduction,
      plainUniformImpl, hsource, sampleSampler,
      offset, shiftSample, shiftSourceSample, sampleToCiphertext,
      map_eq_bind_pure_comp, bind_assoc] using hmapped

/-- The online uniform-source execution is independent of the hidden bit, even for an adaptive
adversary. -/
theorem evalDist_onlineUniform_eq_plain
    (bit : Bool) (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (cloudKey : Encryption.NativeCloudKey q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    evalDist
        (simulateQ
          (GeneralizedSubspaceLWE.Adaptive.sourceImpl
            ($ᵗ GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension))
          (simulateQ (sourceReduction (lweDimension := lweDimension) bit encode)
            (adversary cloudKey))) =
      evalDist (simulateQ
        (plainUniformImpl (Message := Message) (q := q) (lweDimension := lweDimension))
        (adversary cloudKey)) := by
  rw [← QueryImpl.simulateQ_compose]
  exact GeneralizedSubspaceLWE.Adaptive.evalDist_simulateQ_congr
    (GeneralizedSubspaceLWE.Adaptive.sourceImpl
        ($ᵗ GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) lweDimension) ∘ₛ
      sourceReduction (lweDimension := lweDimension) bit encode)
    (plainUniformImpl (Message := Message) (q := q) (lweDimension := lweDimension))
    (evalDist_uniformSource_compose_sourceReduction bit encode)
    (adversary cloudKey)

/-- For a fixed cloud key, a bounded adaptive adversary wins against the uniform query tape with
probability exactly one half. -/
theorem uniformAdaptive_probOutput_true
    (queryCount : ℕ) (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (cloudKey : Encryption.NativeCloudKey q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : IsQueryBoundP (adversary cloudKey)
      (isEncryptionQuery (Message := Message)
        (Ciphertext := TLWE.Ciphertext (ZMod q) lweDimension)) queryCount) :
    Pr[= true | do
      let bit ← $ᵗ Bool
      let transcript ←
        $ᵗ (FormalProof4FHE.LWE.BatchTranscript
          (ZMod q) lweDimension queryCount)
      let guess ← runFromTranscript bit encode adversary cloudKey transcript
      return (bit == guess)] = 1 / 2 := by
  let plainGuess := simulateQ
    (plainUniformImpl (Message := Message) (q := q) (lweDimension := lweDimension))
    (adversary cloudKey)
  have hgame :
      evalDist (do
        let bit ← $ᵗ Bool
        let transcript ←
          $ᵗ (FormalProof4FHE.LWE.BatchTranscript
            (ZMod q) lweDimension queryCount)
        let guess ← runFromTranscript bit encode adversary cloudKey transcript
        return (bit == guess)) =
      evalDist (do
        let bit ← $ᵗ Bool
        let guess ← plainGuess
        return (bit == guess)) := by
    refine evalDist_bind_congr' ($ᵗ Bool) fun bit ↦ ?_
    have htape := evalDist_uniformTranscript_runFromTranscript_eq_online
      queryCount bit encode adversary cloudKey hbound
    have honline := evalDist_onlineUniform_eq_plain bit encode adversary cloudKey
    simpa [plainGuess, bind_assoc] using
      (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (htape.trans honline) (fun guess ↦ pure (bit == guess)))
  rw [evalDist_ext_iff.mp hgame true]
  exact Encryption.Security.fairBit_eq_independentGuess plainGuess

/-- Unshifted adaptive reduction used to expose the information-theoretic uniform branch. -/
noncomputable def zeroCloudReduction
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    LearningWithErrors.Adversary
      (jointLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
        keySwitchErrorSampler inputErrorSampler) :=
  fun transcript ↦ do
    let context ← Native.KeySwitchSecurity.zeroBootstrapContext
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
    transcriptGame encode adversary context.2 transcript

/-- KSK message translation vanishes in the uniform adaptive joint-LWE branch. -/
theorem keySwitchMessageReduction_game1_evalDist_eq_zeroCloud
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (message : RingBinarySecret ringRank degree →
      Fin (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    evalDist (LearningWithErrors.game1
        (jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget message encode adversary)) =
      evalDist (LearningWithErrors.game1
        (jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget encode adversary)) := by
  let samples := Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels
  let contexts := Native.KeySwitchSecurity.zeroBootstrapContext
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [jointLweProblem, MultiQuery.jointLweProblem]
  rw [FormalProof4FHE.LWE.TwoBlock.heterogeneousUniformDistr_eq_uniformSample]
  have hShift := Encryption.Security.uniformTranscript_context_shiftFirst_evalDist
    lweDimension samples queryCount contexts (fun context ↦ message context.1)
    (fun context transcript ↦ transcriptGame encode adversary context.2 transcript)
  simpa [samples, contexts, keySwitchMessageReduction,
      zeroCloudReduction, transcriptGame, bind_assoc, monad_norm] using hShift

/-- The uniform branch of the unshifted adaptive reduction wins with probability one half. -/
theorem jointLwe_game1_probOutput_true
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : IsQueryBound adversary queryCount) :
    Pr[= true | LearningWithErrors.game1
      (jointLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
        keySwitchErrorSampler inputErrorSampler)
      (zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget encode adversary)] = 1 / 2 := by
  let samples := Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels
  let FirstTranscript :=
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension samples
  let SecondTranscript :=
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension queryCount
  let firstTranscripts : ProbComp FirstTranscript := $ᵗ FirstTranscript
  let secondTranscripts : ProbComp SecondTranscript := $ᵗ SecondTranscript
  let contexts := Native.KeySwitchSecurity.zeroBootstrapContext
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
  let finish := fun
      (_context : RingBinarySecret ringRank degree ×
        Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (_first : FirstTranscript) (bit : Bool) (second : SecondTranscript) ↦ do
    let guess ← runFromTranscript bit encode adversary
      ⟨_context.2, _first⟩ second
    return (bit == guess)
  rw [LearningWithErrors.game1]
  simp only [jointLweProblem, MultiQuery.jointLweProblem]
  rw [FormalProof4FHE.LWE.TwoBlock.heterogeneousUniformDistr_eq_uniformSample]
  calc
    _ = Pr[= true | ($ᵗ (FirstTranscript × SecondTranscript)) >>= fun transcripts ↦
        zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget encode adversary
          (FormalProof4FHE.LWE.TwoBlock.ofTranscriptPair transcripts)] := by
      simpa [samples, FirstTranscript, SecondTranscript] using
        (probOutput_bind_bijective_uniform_cross
          (α := FormalProof4FHE.LWE.TwoBlock.Transcript
            (ZMod q) lweDimension samples queryCount)
          (β := FirstTranscript × SecondTranscript)
          FormalProof4FHE.LWE.TwoBlock.toTranscriptPair
          (FormalProof4FHE.LWE.TwoBlock.toTranscriptPair_bijective
            (R := ZMod q) (dimension := lweDimension)
            (firstSamples := samples) (secondSamples := queryCount))
          (fun transcripts ↦
            zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
              tgswGadget encode adversary
              (FormalProof4FHE.LWE.TwoBlock.ofTranscriptPair transcripts)) true)
    _ = Pr[= true | firstTranscripts >>= fun first ↦
        secondTranscripts >>= fun second ↦
        contexts >>= fun context ↦
        ($ᵗ Bool) >>= fun bit ↦
        finish context first bit second] := by
      have uniformProduct :
          ($ᵗ (FirstTranscript × SecondTranscript) :
            ProbComp (FirstTranscript × SecondTranscript)) =
          Prod.mk <$> firstTranscripts <*> secondTranscripts := rfl
      rw [uniformProduct]
      simp [firstTranscripts, secondTranscripts, contexts, finish,
        zeroCloudReduction, transcriptGame, MultiQuery.keySwitchTranscript,
        MultiQuery.inputTranscript,
        FormalProof4FHE.LWE.TwoBlock.ofTranscriptPair,
        FormalProof4FHE.LWE.TwoBlock.toTranscriptPair, monad_norm]
    _ = Pr[= true | firstTranscripts >>= fun first ↦
        contexts >>= fun context ↦
        secondTranscripts >>= fun second ↦
        ($ᵗ Bool) >>= fun bit ↦
        finish context first bit second] := by
      refine probOutput_bind_congr' firstTranscripts true fun first ↦ ?_
      exact probOutput_bind_bind_swap secondTranscripts contexts
        (fun second context ↦
          ($ᵗ Bool) >>= fun bit ↦ finish context first bit second) true
    _ = Pr[= true | firstTranscripts >>= fun first ↦
        contexts >>= fun context ↦
        ($ᵗ Bool) >>= fun bit ↦
        secondTranscripts >>= fun second ↦
        finish context first bit second] := by
      refine probOutput_bind_congr' firstTranscripts true fun first ↦ ?_
      refine probOutput_bind_congr' contexts true fun context ↦ ?_
      exact probOutput_bind_bind_swap secondTranscripts ($ᵗ Bool)
        (fun second bit ↦ finish context first bit second) true
    _ = 1 / 2 := by
      rw [probOutput_bind_eq_tsum]
      calc
        _ = ∑' first, Pr[= first | firstTranscripts] * (1 / 2) := by
          refine tsum_congr fun first : FirstTranscript ↦ ?_
          congr 1
          rw [probOutput_bind_eq_tsum]
          calc
            _ = ∑' context, Pr[= context | contexts] * (1 / 2) := by
              refine tsum_congr fun context : RingBinarySecret ringRank degree ×
                  Native.BootstrappingKey q degree ringRank tgswLevels lweDimension ↦ ?_
              congr 1
              simpa [finish, firstTranscripts, secondTranscripts] using
                (uniformAdaptive_probOutput_true queryCount encode adversary
                  (⟨context.2, first⟩ : Encryption.NativeCloudKey q degree ringRank
                    tgswLevels lweDimension keySwitchLevels)
                  (hbound ⟨context.2, first⟩))
            _ = 1 / 2 := by
              rw [ENNReal.tsum_mul_right,
                tsum_probOutput_eq_one' (by simp [contexts]), one_mul]
        _ = 1 / 2 := by
          rw [ENNReal.tsum_mul_right,
            tsum_probOutput_eq_one' (by simp [firstTranscripts]), one_mul]

/-! ### Final adaptive security bounds -/

/-- The bootstrap-zero adaptive game is game 0 of the native-message joint-LWE reduction. -/
theorem bootstrapZeroGame_evalDist_eq_jointLwe_game0
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    evalDist (bootstrapZeroGame queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary) =
      evalDist (LearningWithErrors.game0
        (jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)) := by
  rw [bootstrapZeroGame_eq_keySwitchMessageGame]
  exact keySwitchMessageGame_evalDist_eq_game0 queryCount
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
    (nativeKeySwitchMessage keySwitchGadget) encode adversary

/-- The actual-message reduction's uniform branch is the fair adaptive oracle game. -/
theorem nativeKeySwitchReduction_game1_probOutput_true
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : IsQueryBound adversary queryCount) :
    Pr[= true | LearningWithErrors.game1
      (jointLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
        keySwitchErrorSampler inputErrorSampler)
      (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)] = 1 / 2 := by
  rw [evalDist_ext_iff.mp
      (keySwitchMessageReduction_game1_evalDist_eq_zeroCloud
        ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
        (nativeKeySwitchMessage keySwitchGadget) encode adversary) true,
    jointLwe_game1_probOutput_true queryCount ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget encode adversary hbound]

/-- The bootstrap-zero adaptive signed advantage is exactly one query-counted joint-LWE
advantage. -/
theorem abs_signedAdvantage_bootstrapZero_eq_jointLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (bootstrapZeroGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| =
      LearningWithErrors.advantage
        (jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold Encryption.signedAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (bootstrapZeroGame_evalDist_eq_jointLwe_game0 queryCount ringErrorSampler
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary)
      true,
    nativeKeySwitchReduction_game1_probOutput_true queryCount ringErrorSampler
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary hbound]
  norm_num

/-- **Query-bounded adaptive native TFHE security up to circular TRGSW.** One cloud-key
replacement plus one shared-secret LWE instance containing every KSK row and exactly
`queryCount` adaptive input rows bounds the honest game. -/
theorem abs_signedAdvantage_real_le_bootstrap_add_jointLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      bootstrapReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
            keySwitchErrorSampler inputErrorSampler)
          (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary) := by
  rw [← abs_signedAdvantage_bootstrapZero_eq_jointLwe queryCount ringErrorSampler
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary hbound]
  exact abs_signedAdvantage_real_le_bootstrap_add_zero queryCount ringErrorSampler
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary

/-- Equal scalar noises flatten the adaptive joint problem exactly to ordinary binary-secret
batch LWE on `keySwitchSamples + queryCount` rows. -/
theorem abs_signedAdvantage_real_le_bootstrap_add_batchLwe_of_same_noise
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realGame queryCount ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      bootstrapReplacementAdvantage queryCount ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
            errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (keySwitchMessageReduction ringErrorSampler errorSampler errorSampler
              tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)) := by
  have h := abs_signedAdvantage_real_le_bootstrap_add_jointLwe queryCount
    ringErrorSampler errorSampler errorSampler tgswGadget keySwitchGadget encode adversary hbound
  have hBatch := FormalProof4FHE.LWE.TwoBlock.advantage_eq_batch
    lweDimension (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels)
    queryCount (Native.sampleLweSecret lweDimension) embedBinarySecret errorSampler
    (keySwitchMessageReduction ringErrorSampler errorSampler errorSampler
      tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)
  change |Encryption.signedAdvantage
      (realGame queryCount ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
    bootstrapReplacementAdvantage queryCount ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary +
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.TwoBlock.problem lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          (Native.sampleLweSecret lweDimension) embedBinarySecret errorSampler)
        (keySwitchMessageReduction ringErrorSampler errorSampler errorSampler
          tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary) at h
  rw [hBatch] at h
  simpa [Native.KeySwitchSecurity.binaryLweProblem] using h

/-- The single adaptive cloud-key replacement is exactly the direct-bilinear KDM advantage of
the whole oracle continuation. -/
theorem bootstrapReplacementAdvantage_eq_directBilinear
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    bootstrapReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary =
      Native.BootstrapSecurity.directBilinearAdvantage
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (continuation queryCount inputErrorSampler encode adversary) := by
  exact Native.BootstrapSecurity.continuationBootstrapReplacementAdvantage_eq_directBilinear
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
    (continuation queryCount inputErrorSampler encode adversary)

/-- Concrete adaptive TFHE security for an allowed, explicitly query-bounded adversary class. -/
def HardAgainst
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary → IsQueryBound adversary queryCount →
    |Encryption.signedAdvantage
      (realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤ bound

/-- Conditional adaptive theorem from direct-bilinear circular/KDM and exact joint LWE. -/
theorem hardAgainst_of_directBilinear_and_jointLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (bootstrapAllowed : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) → Prop)
    (jointLweAllowed : LearningWithErrors.Adversary
      (jointLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
        keySwitchErrorSampler inputErrorSampler) → Prop)
    (bootstrapBound jointLweBound : ℝ)
    (hBootstrapClosed : ∀ adversary, allowed adversary →
      bootstrapAllowed (continuation queryCount inputErrorSampler encode adversary))
    (hJointLweClosed : ∀ adversary, allowed adversary →
      jointLweAllowed
        (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary))
    (hBootstrap : Native.BootstrapSecurity.DirectBilinearHardAgainst
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      bootstrapAllowed bootstrapBound)
    (hJointLwe : FormalProof4FHE.LWE.HardAgainst
      (jointLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
        keySwitchErrorSampler inputErrorSampler)
      jointLweAllowed jointLweBound) :
    HardAgainst queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget encode allowed (bootstrapBound + jointLweBound) := by
  intro adversary hadversary hbound
  calc
    |Encryption.signedAdvantage
        (realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary)| ≤
        bootstrapReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget keySwitchGadget encode adversary +
          LearningWithErrors.advantage
            (jointLweProblem q lweDimension
              (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
              keySwitchErrorSampler inputErrorSampler)
            (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
              tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary) :=
      abs_signedAdvantage_real_le_bootstrap_add_jointLwe queryCount ringErrorSampler
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary hbound
    _ ≤ bootstrapBound + jointLweBound := add_le_add
      (by
        rw [bootstrapReplacementAdvantage_eq_directBilinear queryCount ringErrorSampler
          keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary]
        exact hBootstrap _ (hBootstrapClosed adversary hadversary))
      (hJointLwe _ (hJointLweClosed adversary hadversary))

/-- Equal-noise adaptive adversary-class specialization using ordinary batch LWE on exactly
`keySwitchSamples + queryCount` rows. -/
theorem hardAgainst_of_directBilinear_and_batchLwe_same_noise
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (bootstrapAllowed : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) → Prop)
    (batchLweAllowed : LearningWithErrors.Adversary
      (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
        errorSampler) → Prop)
    (bootstrapBound batchLweBound : ℝ)
    (hBootstrapClosed : ∀ adversary, allowed adversary →
      bootstrapAllowed (continuation queryCount errorSampler encode adversary))
    (hBatchLweClosed : ∀ adversary, allowed adversary →
      batchLweAllowed
        (FormalProof4FHE.LWE.TwoBlock.reduction
          (keySwitchMessageReduction ringErrorSampler errorSampler errorSampler
            tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)))
    (hBootstrap : Native.BootstrapSecurity.DirectBilinearHardAgainst
      ringErrorSampler errorSampler tgswGadget keySwitchGadget
      bootstrapAllowed bootstrapBound)
    (hBatchLwe : FormalProof4FHE.LWE.HardAgainst
      (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
        errorSampler)
      batchLweAllowed batchLweBound) :
    HardAgainst queryCount ringErrorSampler errorSampler errorSampler
      tgswGadget keySwitchGadget encode allowed (bootstrapBound + batchLweBound) := by
  intro adversary hadversary hbound
  calc
    |Encryption.signedAdvantage
        (realGame queryCount ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary)| ≤
        bootstrapReplacementAdvantage queryCount ringErrorSampler errorSampler errorSampler
            tgswGadget keySwitchGadget encode adversary +
          LearningWithErrors.advantage
            (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
              (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
              errorSampler)
            (FormalProof4FHE.LWE.TwoBlock.reduction
              (keySwitchMessageReduction ringErrorSampler errorSampler errorSampler
                tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)) :=
      abs_signedAdvantage_real_le_bootstrap_add_batchLwe_of_same_noise queryCount
        ringErrorSampler errorSampler tgswGadget keySwitchGadget encode adversary hbound
    _ ≤ bootstrapBound + batchLweBound := add_le_add
      (by
        rw [bootstrapReplacementAdvantage_eq_directBilinear queryCount ringErrorSampler
          errorSampler errorSampler tgswGadget keySwitchGadget encode adversary]
        exact hBootstrap _ (hBootstrapClosed adversary hadversary))
      (hBatchLwe _ (hBatchLweClosed adversary hadversary))

end Native

end FormalProof4FHE.TFHE.Encryption.Adaptive
