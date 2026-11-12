module
import all FormalProof4FHE.HasteBoots.LookupCompressionOrdinal
import all FormalProof4FHE.HasteBoots.FirstCompressionCandidate
import all FormalProof4FHE.HasteBoots.FirstCompressionWorkPosition
import all FormalProof4FHE.HasteBoots.FirstCompressionLifetime
import all FormalProof4FHE.HasteBoots.FirstCompressionContinuation
import all FormalProof4FHE.HasteBoots.PrivateCoinFirstCompressionWorkProbability
import all FormalProof4FHE.HasteBoots.CallerLookupWorkCoverage
import all FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability
import all FormalProof4FHE.HasteBoots.CanonicalAllLookupJointPcsLedger
import all FormalProof4FHE.HasteBoots.CanonicalAllLookupJointWorkBound
import all FormalProof4FHE.HasteBoots.LookupMembershipWork
import all FormalProof4FHETest.HasteBootsFirstCompressionWorkSmoke

/-- info: 'FormalProof4FHE.HasteBoots.LookupCompressionOrdinal.original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCompressionOrdinal.original

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionCandidate.budget' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionCandidate.budget

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionCandidate.Candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionCandidate.Candidate

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionCandidate.complexity_le_requests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionCandidate.complexity_le_requests

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionCandidate.budget_of_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionCandidate.budget_of_payload

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionCandidate.ordinal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionCandidate.ordinal

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionCandidate.ordinal_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionCandidate.ordinal_unique

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionWorkPosition.Event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionWorkPosition.Event

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionWorkPosition.SafeEvent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionWorkPosition.SafeEvent

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionWorkPosition.input_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionWorkPosition.input_fixed

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionWorkPosition.budget_rate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionWorkPosition.budget_rate

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionWorkPosition.conditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionWorkPosition.conditional

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionWorkPosition.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionWorkPosition.bound

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionLifetime.Event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionLifetime.Event

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionLifetime.safe_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionLifetime.safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionLifetime.private_safe_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionLifetime.private_safe_probability

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionContinuation.candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionContinuation.candidate

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionContinuation.event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionContinuation.event

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionContinuation.lifetime_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionContinuation.lifetime_event

/-- info: 'FormalProof4FHE.HasteBoots.FirstCompressionContinuation.private_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FirstCompressionContinuation.private_monotone

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinFirstCompressionWorkProbability.Event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinFirstCompressionWorkProbability.Event

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinFirstCompressionWorkProbability.Bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinFirstCompressionWorkProbability.Bad

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinFirstCompressionWorkProbability.prefix_safe_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinFirstCompressionWorkProbability.prefix_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinFirstCompressionWorkProbability.safe_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinFirstCompressionWorkProbability.safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinFirstCompressionWorkProbability.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinFirstCompressionWorkProbability.bound

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinFirstCompressionWorkProbability.safe_work_132' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinFirstCompressionWorkProbability.safe_work_132

/-- info: 'FormalProof4FHE.HasteBoots.CallerLookupWorkCoverage.recover_compression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CallerLookupWorkCoverage.recover_compression

/-- info: 'FormalProof4FHE.HasteBoots.CallerLookupWorkCoverage.compression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CallerLookupWorkCoverage.compression

/-- info: 'FormalProof4FHE.HasteBoots.CallerLookupWorkCoverage.nonmember' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CallerLookupWorkCoverage.nonmember

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability.rate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability.rate

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability.Event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability.Event

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability.Bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability.Bad

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability.safe_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability.safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability.finiteRate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability.finiteRate

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability.finite_rate_coe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability.finite_rate_coe

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability.rate_le_130' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability.rate_le_130

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability.safe_work_130' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinAllLookupChallengeProbability.safe_work_130

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalAllLookupJointPcsLedger.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalAllLookupJointPcsLedger.bound

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalAllLookupJointWorkBound.rate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalAllLookupJointWorkBound.rate

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalAllLookupJointWorkBound.finiteRate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalAllLookupJointWorkBound.finiteRate

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalAllLookupJointWorkBound.finite_rate_coe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalAllLookupJointWorkBound.finite_rate_coe

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalAllLookupJointWorkBound.rate_le_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalAllLookupJointWorkBound.rate_le_128

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalAllLookupJointWorkBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalAllLookupJointWorkBound.bound

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalAllLookupJointWorkBound.work_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalAllLookupJointWorkBound.work_128

/-- info: 'FormalProof4FHE.HasteBoots.LookupMembershipWork.Witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupMembershipWork.Witness

/-- info: 'FormalProof4FHE.HasteBoots.LookupMembershipWork.Failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupMembershipWork.Failure

/-- info: 'FormalProof4FHE.HasteBoots.LookupMembershipWork.rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupMembershipWork.rate

/-- info: 'FormalProof4FHE.HasteBoots.LookupMembershipWork.covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupMembershipWork.covered

/-- info: 'FormalProof4FHE.HasteBoots.LookupMembershipWork.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupMembershipWork.bound

/-- info: 'FormalProof4FHE.HasteBoots.LookupMembershipWork.rate_le_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupMembershipWork.rate_le_128

/-- info: 'FormalProof4FHE.HasteBoots.LookupMembershipWork.work_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupMembershipWork.work_128

/-- info: '_private.FormalProof4FHETest.HasteBootsFirstCompressionWorkSmoke.0.HasteBootsFirstCompressionWorkSmoke.request' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsFirstCompressionWorkSmoke.request

/-- info: '_private.FormalProof4FHETest.HasteBootsFirstCompressionWorkSmoke.0.HasteBootsFirstCompressionWorkSmoke.repetitions_share_payload' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsFirstCompressionWorkSmoke.repetitions_share_payload

/-- info: '_private.FormalProof4FHETest.HasteBootsFirstCompressionWorkSmoke.0.HasteBootsFirstCompressionWorkSmoke.width_one_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsFirstCompressionWorkSmoke.width_one_injective

/-- info: '_private.FormalProof4FHETest.HasteBootsFirstCompressionWorkSmoke.0.HasteBootsFirstCompressionWorkSmoke.badSource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsFirstCompressionWorkSmoke.badSource

/-- info: '_private.FormalProof4FHETest.HasteBootsFirstCompressionWorkSmoke.0.HasteBootsFirstCompressionWorkSmoke.publicTable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsFirstCompressionWorkSmoke.publicTable

/-- info: '_private.FormalProof4FHETest.HasteBootsFirstCompressionWorkSmoke.0.HasteBootsFirstCompressionWorkSmoke.collision_can_pass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsFirstCompressionWorkSmoke.collision_can_pass
