module
public import FormalProof4FHE.HasteBoots.BatchColumnContextName
@[expose] public section

/-! Attained source parameters are fixed across an original first-column
replay fiber outside the existing hash/late-context ledger. Original code
origins and role admission are retained, not chosen by dimension matching. -/
namespace FormalProof4FHE.HasteBoots.BatchColumnParameterCandidate
open InputIndexedOracle (Input World)
open OracleProgram (Program run runPrefix)
open NativeRootMessage (Digest)
noncomputable section

def select {A : Type} (packet : (Program A ⊕ A) × List NativeTranscript.Observation) : Option NativeGoldBatchChallengeLink.View :=
  (CausalStreamExposure.firstRead OracleProgramMachine.step packet).bind NativeGoldBatchChallengeLink.parse

structure Candidate {A : Type} (program : Program A) (position : ℕ) (profile : Digest) (world : World) where
  ctx : NativeGoldBatchPcsProgram.Context
  origin : CacheBackedCodeOrigin.Origin ctx
  role : NativeBrakedownCalibration.Role
  admitted : NativeGoldBatchCalibration.Matches ctx role
  profile_eq : ctx.parent.profile = profile
  input : Input
  decoded : NativeGoldBatchChallengeLink.View
  parsed : NativeGoldBatchChallengeLink.parse input = some decoded
  first : ProgramFirstStreamRead.First program world input
  atFirst : first.position = position
  computed : (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some decoded.field.data.context
  full : (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.2.Sublist (run program world).run.2

def extend {A B : Type} {program : Program A} {position : ℕ} {profile : Digest} {world : World}
    (candidate : Candidate program position profile world) (next : A → Program B) : Candidate (OracleProgram.bind program next) position profile world where
  ctx := candidate.ctx
  origin := candidate.origin
  role := candidate.role
  admitted := candidate.admitted
  profile_eq := candidate.profile_eq
  input := candidate.input
  decoded := candidate.decoded
  parsed := candidate.parsed
  first := ProgramContinuationPrefix.first candidate.first next
  atFirst := candidate.atFirst
  computed := candidate.computed
  full := candidate.full.trans (ProgramContinuationPrefix.log_prefix program next world).sublist

theorem selected {A : Type} {program : Program A} {position : ℕ} {profile : Digest} {world : World}
    (candidate : Candidate program position profile world) :
    select (runPrefix position program world).run = some candidate.decoded := by
  have first := candidate.first.selected
  rw [candidate.atFirst] at first
  simp only [select,first,Option.bind_some,candidate.parsed]

theorem parameters_or_bad {A : Type} (program : Program A) (position : ℕ) (profile dummy : Digest) (world other : World)
    (left : Candidate program position profile world) (right : Candidate program position profile other)
    (same : (runPrefix position program other).run = (runPrefix position program world).run) :
    left.ctx.parameters = right.ctx.parameters ∨ NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2 ∨
      ProgramContextTarget.Bad program world ∨ ProgramContextTarget.Bad program other := by
  have fields : left.decoded = right.decoded := by
    have ls := selected left
    have rs := selected right
    rw [same] at rs
    exact Option.some.inj (ls.symm.trans rs)
  have leftObserved := ContextAtFirstRead.observed_or_bad program world left.input left.first left.ctx.parameters left.decoded.field.data.context
    left.computed left.full (BatchColumnContextName.context left.input left.decoded left.parsed)
  have rightObserved := ContextAtFirstRead.observed_or_bad program other right.input right.first right.ctx.parameters right.decoded.field.data.context
    right.computed right.full (BatchColumnContextName.context right.input right.decoded right.parsed)
  rw [left.atFirst] at leftObserved
  rw [right.atFirst] at rightObserved
  rcases leftObserved with leftBefore | bad
  · rcases rightObserved with rightBefore | bad
    · have computed : (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row right.ctx.parameters) other).run.1 = some left.decoded.field.data.context := by
        rw [fields]
        exact right.computed
      rcases GoldContextFiber.parameters_or_bad (OracleProgram.prefix_replay position program) world other _ _ left.decoded.field.data.context dummy
        left.computed computed leftBefore rightBefore same with equal | bad
      · exact Or.inl equal
      · exact Or.inr (Or.inl bad)
    · exact Or.inr (Or.inr (Or.inr bad))
  · exact Or.inr (Or.inr (Or.inl bad))

theorem parameters {A : Type} (program : Program A) (position : ℕ) (profile dummy : Digest) (world other : World)
    (left : Candidate program position profile world) (right : Candidate program position profile other)
    (same : (runPrefix position program other).run = (runPrefix position program world).run)
    (leftSafe : ¬GlobalReferenceBad.Bad program dummy world) (rightSafe : ¬GlobalReferenceBad.Bad program dummy other) :
    left.ctx.parameters = right.ctx.parameters := by
  have good := GlobalReferenceBad.good program position dummy world leftSafe
  have otherGood := GlobalReferenceBad.good program position dummy other rightSafe
  rcases parameters_or_bad program position profile dummy world other left right same with equal | root | late | late
  · exact equal
  · exact False.elim (good.root root)
  · exact False.elim (good.context late)
  · exact False.elim (otherGood.context late)

theorem radius_eq {A : Type} {program : Program A} {position : ℕ} {profile : Digest} {world other : World}
    (left : Candidate program position profile world) (right : Candidate program position profile other)
    (same : left.ctx.parameters = right.ctx.parameters) :
    NativeBrakedownCalibration.radius .goldilocks left.role = NativeBrakedownCalibration.radius .goldilocks right.role := by
  unfold NativeBrakedownCalibration.radius
  rw [← left.admitted.height,← left.admitted.message,← right.admitted.height,← right.admitted.message,same]

end
end FormalProof4FHE.HasteBoots.BatchColumnParameterCandidate
