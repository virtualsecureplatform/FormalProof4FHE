module
public import FormalProof4FHE.HasteBoots.CanonicalCandidateScalarTest
public import FormalProof4FHE.HasteBoots.LookupViewSumReduction
@[expose] public section

/-! The original even message and canonical helper family determine the sum
challenge test. Existing attained-family fixation fixes its honest polynomial. -/
namespace FormalProof4FHE.HasteBoots.CanonicalSumCandidate
open InputIndexedOracle (World)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open NativeExtensionFields (Goldilocks3)
open JobReferenceCandidate (Candidate)
open CanonicalCandidateFixation (Fixed)
open MeasureTheory ProbabilityTheory
noncomputable section

abbrev info {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) := LookupScalarGrammar.sumInfo candidate.selection.origin.geometry.geometry.1

abbrev dimension {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) := CanonicalCandidateScalarTest.dimension candidate

def tables {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) :=
  LookupViewSumReduction.tables (CanonicalCandidateFixation.helpers candidate dummy)

theorem sum_info {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) :
    candidate.selection.origin.ready.statement.infos.val[2*candidate.selection.index.val]? = some (info candidate) := by
  exact (LookupScalarGrammar.protocol_pair candidate.selection.ctx.requests.property.le
    (NativeSharedLookupParent.models candidate.selection.ctx.requests) candidate.selection.origin.geometry.geometry.1
    candidate.selection.ctx.proof.values.multiplicities candidate.selection.ctx.proof.values.roots
    candidate.selection.ctx.proof.roots.property 7 candidate.selection.ctx.lookupFuel candidate.selection.ctx.equalityFuel
    (LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row candidate.selection.ctx.registry
      candidate.selection.ctx.helper candidate.selection.ctx.parent candidate.selection.ctx.requests candidate.selection.ctx.proof world)
    world candidate.selection.origin.ready candidate.selection.origin.prepared candidate.selection.index.val candidate.selection.index.isLt).1

theorem same_info {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other)
    (input : left.selection.family.input = right.selection.family.input) (ordinal : left.selection.index.val = right.selection.index.val) :
    info left = info right := by
  have metadata := sum_info left
  rw [(CandidateScalarPacket.compare left right input).2.1,ordinal,sum_info right] at metadata
  exact Option.some.inj metadata.symm

theorem same_message {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other)
    (input : left.selection.family.input = right.selection.family.input) (ordinal : left.selection.index.val = right.selection.index.val)
    (lm rm : NativeScalarBatchWire.Message)
    (leftAt : (CandidateScalarPacket.reader left).entry.packet.messages.val[2*left.selection.index.val]? = some lm)
    (rightAt : (CandidateScalarPacket.reader right).entry.packet.messages.val[2*right.selection.index.val]? = some rm) : lm = rm := by
  have packet := (CandidateScalarPacket.compare left right input).2.2
  rw [packet,ordinal,rightAt] at leftAt
  exact Option.some.inj leftAt.symm

theorem helper_tables {ln rn lp rp : ℕ}
    (left : MatrixFold.Cube ln → Fin (3+lp) → NativeFields.Goldilocks)
    (right : MatrixFold.Cube rn → Fin (3+rp) → NativeFields.Goldilocks)
    (dimensions : ln = rn) (padding : lp = rp) (helpers : HEq left right) :
    HEq (LookupViewSumReduction.tables left) (LookupViewSumReduction.tables right) := by
  subst rn rp
  cases helpers
  rfl

theorem tables_fixed {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (ordinal : left.selection.index.val = right.selection.index.val) (fixed : Fixed left right dummy) :
    HEq (tables left dummy) (tables right dummy) := by
  have aligned := CanonicalCandidateTables.alignment left right dummy ordinal fixed
  exact helper_tables _ _ (by rw [aligned.padding,aligned.rows]) aligned.helperPadding fixed.families.2

theorem honest_fixed {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (ordinal : left.selection.index.val = right.selection.index.val) (fixed : Fixed left right dummy)
    (prior : List NativeGoldExtensionArithmetic.Word) :
    ScalarNativeSourceHealing.honest ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices
      (dimension left) (tables left dummy) prior =
    ScalarNativeSourceHealing.honest ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices
      (dimension right) (tables right dummy) prior := by
  have aligned := CanonicalCandidateTables.alignment left right dummy ordinal fixed
  exact LookupIdentityTableCongruence.honest _ _ _ _ _ _ (by rw [aligned.padding,aligned.rows])
    (tables_fixed left right dummy ordinal fixed) rfl prior

abbrev test {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) (message : NativeScalarBatchWire.Message) :=
  ScalarSourceChallengeBound.test (info candidate) message ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient
    ScalarLookupExpression.sumIndices (dimension candidate) (tables candidate dummy)

theorem test_fixed {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (input : left.selection.family.input = right.selection.family.input) (ordinal : left.selection.index.val = right.selection.index.val)
    (fixed : Fixed left right dummy) (lm rm : NativeScalarBatchWire.Message)
    (leftAt : (CandidateScalarPacket.reader left).entry.packet.messages.val[2*left.selection.index.val]? = some lm)
    (rightAt : (CandidateScalarPacket.reader right).entry.packet.messages.val[2*right.selection.index.val]? = some rm) :
    test left dummy lm = test right dummy rm := by
  have metadata := same_info left right input ordinal
  have message := same_message left right input ordinal lm rm leftAt rightAt
  funext prior value
  unfold test ScalarSourceChallengeBound.test ScalarSourceChallengeBound.Eligible ScalarSourceChallengeBound.correct
  rw [metadata,message,honest_fixed left right dummy ordinal fixed prior.2.1]

theorem bound {A : Type} (program : Program A) (position : ℕ) (world : World)
    (candidate : Candidate program position world) (dummy profile : Digest) (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover candidate.selection.family.input = some configuration)
    (message : NativeScalarBatchWire.Message) :
    (InputIndexedOracle.law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}])
      {other | ScalarRecoveredUnboundedLaw.event candidate.selection.family.input configuration profile (test candidate dummy message) other} ≤
      (1 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) := by
  simpa only [test,info,LookupScalarGrammar.sumInfo,Nat.cast_one] using
    (RefinedScalarSourceKernel.source_bound program position world candidate dummy profile configuration found
      (info candidate) message ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices
      (dimension candidate) (tables candidate dummy))

end
end FormalProof4FHE.HasteBoots.CanonicalSumCandidate
