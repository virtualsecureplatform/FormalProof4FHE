module
import all FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix
import all FormalProof4FHE.HasteBoots.LookupCompressionCount
import all FormalProof4FHE.HasteBoots.LookupOffsetOrdinal
import all FormalProof4FHE.HasteBoots.OffsetPositionKernel
import all FormalProof4FHE.HasteBoots.OffsetDegreeBudget
import all FormalProof4FHE.HasteBoots.OffsetPositionContinuation
import all FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability
import all FormalProof4FHE.HasteBoots.CallerOffsetPositionCoverage
import all FormalProof4FHETest.HasteBootsOffsetPositionSmoke

/-- info: 'FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix.emitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix.emitted

/-- info: 'FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix.Indexed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix.Indexed

/-- info: 'FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix.append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix.append

/-- info: 'FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix.Certificates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix.Certificates

/-- info: 'FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix.after_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix.after_sample

/-- info: 'FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix.tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix.tick

/-- info: 'FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix.execute

/-- info: 'FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix.initialized

/-- info: 'FormalProof4FHE.HasteBoots.LookupCompressionCount.count' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCompressionCount.count

/-- info: 'FormalProof4FHE.HasteBoots.LookupCompressionCount.fromInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCompressionCount.fromInput

/-- info: 'FormalProof4FHE.HasteBoots.LookupCompressionCount.append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCompressionCount.append

/-- info: 'FormalProof4FHE.HasteBoots.LookupCompressionCount.group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCompressionCount.group

/-- info: 'FormalProof4FHE.HasteBoots.LookupCompressionCount.emitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCompressionCount.emitted

/-- info: 'FormalProof4FHE.HasteBoots.LookupCompressionCount.identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCompressionCount.identity

/-- info: 'FormalProof4FHE.HasteBoots.LookupCompressionCount.start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCompressionCount.start

/-- info: 'FormalProof4FHE.HasteBoots.LookupOffsetOrdinal.at_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupOffsetOrdinal.at_last

/-- info: 'FormalProof4FHE.HasteBoots.LookupOffsetOrdinal.original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupOffsetOrdinal.original

/-- info: 'FormalProof4FHE.HasteBoots.LookupOffsetOrdinal.candidate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupOffsetOrdinal.candidate

/-- info: 'FormalProof4FHE.HasteBoots.LookupOffsetOrdinal.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupOffsetOrdinal.unique

/-- info: 'FormalProof4FHE.HasteBoots.OffsetPositionKernel.SafeEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetPositionKernel.SafeEvent

/-- info: 'FormalProof4FHE.HasteBoots.OffsetPositionKernel.Event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetPositionKernel.Event

/-- info: 'FormalProof4FHE.HasteBoots.OffsetPositionKernel.BoundedEvent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetPositionKernel.BoundedEvent

/-- info: 'FormalProof4FHE.HasteBoots.OffsetPositionKernel.safe_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetPositionKernel.safe_iff

/-- info: 'FormalProof4FHE.HasteBoots.OffsetPositionKernel.input_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetPositionKernel.input_fixed

/-- info: 'FormalProof4FHE.HasteBoots.OffsetPositionKernel.indices_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetPositionKernel.indices_fixed

/-- info: 'FormalProof4FHE.HasteBoots.OffsetPositionKernel.cost_alternative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetPositionKernel.cost_alternative

/-- info: 'FormalProof4FHE.HasteBoots.OffsetPositionKernel.conditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetPositionKernel.conditional

/-- info: 'FormalProof4FHE.HasteBoots.OffsetPositionKernel.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetPositionKernel.bound

/-- info: 'FormalProof4FHE.HasteBoots.OffsetDegreeBudget.budget' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetDegreeBudget.budget

/-- info: 'FormalProof4FHE.HasteBoots.OffsetDegreeBudget.complexity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetDegreeBudget.complexity

/-- info: 'FormalProof4FHE.HasteBoots.OffsetDegreeBudget.event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetDegreeBudget.event

/-- info: 'FormalProof4FHE.HasteBoots.OffsetPositionContinuation.event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetPositionContinuation.event

/-- info: 'FormalProof4FHE.HasteBoots.OffsetPositionContinuation.private_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OffsetPositionContinuation.private_monotone

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability.Event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability.Event

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability.Bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability.Bad

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability.prefix_safe_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability.prefix_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability.safe_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability.safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability.bound

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability.OriginalEvent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability.OriginalEvent

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability.original_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability.original_iff

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability.original_safe_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability.original_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.CallerOffsetPositionCoverage.reciprocal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CallerOffsetPositionCoverage.reciprocal

/-- info: 'FormalProof4FHE.HasteBoots.CallerOffsetPositionCoverage.nonmember' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CallerOffsetPositionCoverage.nonmember

/-- info: '_private.FormalProof4FHETest.HasteBootsOffsetPositionSmoke.0.HasteBootsOffsetPositionSmoke.identity' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsOffsetPositionSmoke.identity

/-- info: '_private.FormalProof4FHETest.HasteBootsOffsetPositionSmoke.0.HasteBootsOffsetPositionSmoke.compression' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsOffsetPositionSmoke.compression

/-- info: '_private.FormalProof4FHETest.HasteBootsOffsetPositionSmoke.0.HasteBootsOffsetPositionSmoke.offset' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsOffsetPositionSmoke.offset

/-- info: '_private.FormalProof4FHETest.HasteBootsOffsetPositionSmoke.0.HasteBootsOffsetPositionSmoke.retries_do_not_change_job_marker' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsOffsetPositionSmoke.retries_do_not_change_job_marker

/-- info: '_private.FormalProof4FHETest.HasteBootsOffsetPositionSmoke.0.HasteBootsOffsetPositionSmoke.repeated_jobs_remain_distinct' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsOffsetPositionSmoke.repeated_jobs_remain_distinct

/-- info: '_private.FormalProof4FHETest.HasteBootsOffsetPositionSmoke.0.HasteBootsOffsetPositionSmoke.metadataMarker' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsOffsetPositionSmoke.metadataMarker

/-- info: '_private.FormalProof4FHETest.HasteBootsOffsetPositionSmoke.0.HasteBootsOffsetPositionSmoke.metadata_is_not_a_job' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsOffsetPositionSmoke.metadata_is_not_a_job
