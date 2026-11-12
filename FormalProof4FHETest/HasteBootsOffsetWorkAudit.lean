module
import all FormalProof4FHE.HasteBoots.LookupStreamWorkRate
import all FormalProof4FHE.HasteBoots.OffsetWorkPosition
import all FormalProof4FHE.HasteBoots.OffsetLifetimeWork
import all FormalProof4FHE.HasteBoots.PrivateCoinOffsetWorkProbability
import all FormalProof4FHE.HasteBoots.PrivateCoinLookupChallengeProbability
import all FormalProof4FHE.HasteBoots.CallerOffsetWorkCoverage
import all FormalProof4FHETest.HasteBootsOffsetWorkSmoke

/-- info: 'FormalProof4FHE.HasteBoots.LookupStreamWorkRate.rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupStreamWorkRate.rate

/-- info: 'FormalProof4FHE.HasteBoots.LookupStreamWorkRate.key_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupStreamWorkRate.key_length

/-- info: 'FormalProof4FHE.HasteBoots.LookupStreamWorkRate.budget_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupStreamWorkRate.budget_rate

/-- info: 'FormalProof4FHE.HasteBoots.LookupStreamWorkRate.input_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupStreamWorkRate.input_rate

/-- info: 'FormalProof4FHE.HasteBoots.OffsetWorkPosition.score' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetWorkPosition.score

/-- info: 'FormalProof4FHE.HasteBoots.OffsetWorkPosition.charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetWorkPosition.charge

/-- info: 'FormalProof4FHE.HasteBoots.OffsetWorkPosition.Event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetWorkPosition.Event

/-- info: 'FormalProof4FHE.HasteBoots.OffsetWorkPosition.conditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetWorkPosition.conditional

/-- info: 'FormalProof4FHE.HasteBoots.OffsetWorkPosition.charge_measurable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetWorkPosition.charge_measurable

/-- info: 'FormalProof4FHE.HasteBoots.OffsetWorkPosition.charge_seen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetWorkPosition.charge_seen

/-- info: 'FormalProof4FHE.HasteBoots.OffsetWorkPosition.charge_finished' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetWorkPosition.charge_finished

/-- info: 'FormalProof4FHE.HasteBoots.OffsetWorkPosition.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetWorkPosition.bound

/-- info: 'FormalProof4FHE.HasteBoots.OffsetLifetimeWork.Event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetLifetimeWork.Event

/-- info: 'FormalProof4FHE.HasteBoots.OffsetLifetimeWork.totalCharge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetLifetimeWork.totalCharge

/-- info: 'FormalProof4FHE.HasteBoots.OffsetLifetimeWork.safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetLifetimeWork.safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.OffsetLifetimeWork.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetLifetimeWork.bound

/-- info: 'FormalProof4FHE.HasteBoots.OffsetLifetimeWork.charge_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetLifetimeWork.charge_eq

/-- info: 'FormalProof4FHE.HasteBoots.OffsetLifetimeWork.program_charge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetLifetimeWork.program_charge

/-- info: 'FormalProof4FHE.HasteBoots.OffsetLifetimeWork.private_prefix_charge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetLifetimeWork.private_prefix_charge

/-- info: 'FormalProof4FHE.HasteBoots.OffsetLifetimeWork.private_safe_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetLifetimeWork.private_safe_probability

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinOffsetWorkProbability.Event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinOffsetWorkProbability.Event

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinOffsetWorkProbability.Bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinOffsetWorkProbability.Bad

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinOffsetWorkProbability.prefix_safe_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinOffsetWorkProbability.prefix_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinOffsetWorkProbability.safe_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinOffsetWorkProbability.safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinOffsetWorkProbability.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinOffsetWorkProbability.bound

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinOffsetWorkProbability.safe_work_132' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinOffsetWorkProbability.safe_work_132

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinLookupChallengeProbability.rate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinLookupChallengeProbability.rate

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinLookupChallengeProbability.Event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinLookupChallengeProbability.Event

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinLookupChallengeProbability.Bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinLookupChallengeProbability.Bad

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinLookupChallengeProbability.safe_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinLookupChallengeProbability.safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.CallerOffsetWorkCoverage.reciprocal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CallerOffsetWorkCoverage.reciprocal

/-- info: 'FormalProof4FHE.HasteBoots.CallerOffsetWorkCoverage.nonmember' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CallerOffsetWorkCoverage.nonmember

/-- info: '_private.FormalProof4FHETest.HasteBootsOffsetWorkSmoke.0.HasteBootsOffsetWorkSmoke.once' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsOffsetWorkSmoke.once

/-- info: '_private.FormalProof4FHETest.HasteBootsOffsetWorkSmoke.0.HasteBootsOffsetWorkSmoke.repeated' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsOffsetWorkSmoke.repeated

/-- info: '_private.FormalProof4FHETest.HasteBootsOffsetWorkSmoke.0.HasteBootsOffsetWorkSmoke.empty' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsOffsetWorkSmoke.empty

/-- info: '_private.FormalProof4FHETest.HasteBootsOffsetWorkSmoke.0.HasteBootsOffsetWorkSmoke.partial_prequery_paid_once' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsOffsetWorkSmoke.partial_prequery_paid_once

/-- info: '_private.FormalProof4FHETest.HasteBootsOffsetWorkSmoke.0.HasteBootsOffsetWorkSmoke.empty_read_not_charged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsOffsetWorkSmoke.empty_read_not_charged

/-- info: '_private.FormalProof4FHETest.HasteBootsOffsetWorkSmoke.0.HasteBootsOffsetWorkSmoke.one_read_lifetime_charge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsOffsetWorkSmoke.one_read_lifetime_charge
