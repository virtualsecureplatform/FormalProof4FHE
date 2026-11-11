module
public import FormalProof4FHE.HasteBoots.SingleOpeningFalseClaimWitness
public import FormalProof4FHE.HasteBoots.SingleOpeningConcreteColumnBound
@[expose] public section

/-! Near false-claim and far random-row witnesses enter the same concrete
single-opening family at its minimum distance, with no lane union factor. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningConcreteColumnWitness
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsProgram (Scheduler)
open InputIndexedOracle (World)
open NativeTranscript (Observation)
open NativeRootMessage (Digest)
open NativeRootFamilySourceSelection (Log)
open SingleOpeningConcreteColumnFamily (source raw claim Test Position Symbol Domain)
open SingleOpeningConcreteColumnBound (distance)
open SingleOpeningFixedResponseData (left right claimed)
noncomputable section

theorem near_distance {Memory : Type} {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (dummy : Digest) (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample) (origin : CacheBackedSingleOpening.Origin ctx)
    (history : List Observation) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (accepted : SingleOpeningAvailability.Accepted world history ctx choose fuel memory work)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded)
    (sourceLog : Log) (state : NativeFieldVector.State) (radius : ℕ)
    (near : ∃ close, CommonSource.RowsIn (BlockCode.code (Domain ctx origin.primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val) close ∧
        hammingDist (source dummy ctx decoded sourceLog) close ≤ radius)
    (falseClaim : claimed ctx decoded.field.data.claimed ≠ matrixEvaluation
      (left ctx.parameters decoded.field.data.query) (right ctx.parameters decoded.field.data.query)
      (RectangularMatrixOpeningKernel.extract (Domain ctx origin.primitive) origin.capacity radius (source dummy ctx decoded sourceLog))) :
    ∃ test : Test ctx, distance ctx origin.primitive radius ≤
      hammingDist (raw dummy ctx decoded sourceLog state test) (claim ctx origin.primitive decoded state test) := by
  have branch := SingleOpeningFalseClaimWitness.near_witness receipt origin history choose fuel memory accepted responseFits decoded parsed
    radius (source dummy ctx decoded sourceLog) near falseClaim
  obtain ⟨test,bounded⟩ := SingleOpeningConcreteColumnFamily.structured_witness dummy ctx origin.primitive decoded sourceLog state _ branch
  exact ⟨test,(Nat.min_le_left _ _).trans bounded⟩

theorem far_distance (dummy : Digest) (ctx : Context) [NeZero ctx.parameters.code.blockWidth.val]
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)))
    (decoded : SingleOpeningChallengeLink.View) (sourceLog : Log) (state : NativeFieldVector.State) (radius : ℕ)
    (outside : ¬∀ lane : Fin ctx.parameters.width.val,
      Code.distFromCode (StructuredOpening.combine (SingleOpeningRecoveredMatrix.random ctx state lane) (source dummy ctx decoded sourceLog))
        (BlockCode.code (Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
          Set (Position ctx → Symbol ctx)) ≤ radius) :
    ∃ test : Test ctx, distance ctx primitive radius ≤
      hammingDist (raw dummy ctx decoded sourceLog state test) (claim ctx primitive decoded state test) := by
  have branch := RectangularMatrixDisagreement.far_witness (Domain ctx primitive) radius ctx.parameters.width.val
    (source dummy ctx decoded sourceLog) (SingleOpeningRecoveredMatrix.random ctx state)
    (fun lane => claim ctx primitive decoded state (.inl lane))
    (fun lane => SingleOpeningConcreteColumnFamily.coded ctx primitive decoded state (.inl lane)) outside
  obtain ⟨test,bounded⟩ := SingleOpeningConcreteColumnFamily.random_witness dummy ctx primitive decoded sourceLog state _ branch
  exact ⟨test,(Nat.min_le_right _ _).trans bounded⟩

end
end FormalProof4FHE.HasteBoots.SingleOpeningConcreteColumnWitness
