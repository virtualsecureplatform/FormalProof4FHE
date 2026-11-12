module
import all FormalProof4FHE.HasteBoots.LookupInputSeparation
import all FormalProof4FHE.HasteBoots.RefinedCompressionKernel
import all FormalProof4FHE.HasteBoots.CompressionClassKernel
import all FormalProof4FHE.HasteBoots.CompressionContinuation
import all FormalProof4FHE.HasteBoots.CallerCompressionClassRecovery
import all FormalProof4FHE.HasteBoots.PrivateCoinCompressionClassProbability
import all FormalProof4FHETest.HasteBootsRefinedCompressionSmoke

/-- info: 'FormalProof4FHE.HasteBoots.LookupInputSeparation.begin_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupInputSeparation.begin_rejected

/-- info: 'FormalProof4FHE.HasteBoots.LookupInputSeparation.drive_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupInputSeparation.drive_input

/-- info: 'FormalProof4FHE.HasteBoots.LookupInputSeparation.finished_framed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupInputSeparation.finished_framed

/-- info: 'FormalProof4FHE.HasteBoots.LookupInputSeparation.Separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupInputSeparation.Separated

/-- info: 'FormalProof4FHE.HasteBoots.LookupInputSeparation.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupInputSeparation.initial

/-- info: 'FormalProof4FHE.HasteBoots.LookupInputSeparation.tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupInputSeparation.tick

/-- info: 'FormalProof4FHE.HasteBoots.LookupInputSeparation.BatchSeparated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupInputSeparation.BatchSeparated

/-- info: 'FormalProof4FHE.HasteBoots.LookupInputSeparation.after_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupInputSeparation.after_sample

/-- info: 'FormalProof4FHE.HasteBoots.LookupInputSeparation.batch_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupInputSeparation.batch_tick

/-- info: 'FormalProof4FHE.HasteBoots.LookupInputSeparation.batch_execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupInputSeparation.batch_execute

/-- info: 'FormalProof4FHE.HasteBoots.LookupInputSeparation.original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupInputSeparation.original

/-- info: 'FormalProof4FHE.HasteBoots.RefinedCompressionKernel.complexity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RefinedCompressionKernel.complexity

/-- info: 'FormalProof4FHE.HasteBoots.RefinedCompressionKernel.rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RefinedCompressionKernel.rate

/-- info: 'FormalProof4FHE.HasteBoots.RefinedCompressionKernel.input_frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RefinedCompressionKernel.input_frames

/-- info: 'FormalProof4FHE.HasteBoots.RefinedCompressionKernel.unseen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RefinedCompressionKernel.unseen

/-- info: 'FormalProof4FHE.HasteBoots.RefinedCompressionKernel.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RefinedCompressionKernel.selected

/-- info: 'FormalProof4FHE.HasteBoots.RefinedCompressionKernel.complexity_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RefinedCompressionKernel.complexity_fixed

/-- info: 'FormalProof4FHE.HasteBoots.RefinedCompressionKernel.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RefinedCompressionKernel.bound

/-- info: 'FormalProof4FHE.HasteBoots.RefinedCompressionKernel.bound_of_complexity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RefinedCompressionKernel.bound_of_complexity

/-- info: 'FormalProof4FHE.HasteBoots.CompressionClassKernel.Class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionClassKernel.Class

/-- info: 'FormalProof4FHE.HasteBoots.CompressionClassKernel.Event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionClassKernel.Event

/-- info: 'FormalProof4FHE.HasteBoots.CompressionClassKernel.SafeEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionClassKernel.SafeEvent

/-- info: 'FormalProof4FHE.HasteBoots.CompressionClassKernel.Lifetime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionClassKernel.Lifetime

/-- info: 'FormalProof4FHE.HasteBoots.CompressionClassKernel.of_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionClassKernel.of_candidate

/-- info: 'FormalProof4FHE.HasteBoots.CompressionClassKernel.cost_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionClassKernel.cost_unique

/-- info: 'FormalProof4FHE.HasteBoots.CompressionClassKernel.covered_conditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionClassKernel.covered_conditional

/-- info: 'FormalProof4FHE.HasteBoots.CompressionClassKernel.conditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionClassKernel.conditional

/-- info: 'FormalProof4FHE.HasteBoots.CompressionClassKernel.cost_alternative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionClassKernel.cost_alternative

/-- info: 'FormalProof4FHE.HasteBoots.CompressionClassKernel.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionClassKernel.bound

/-- info: 'FormalProof4FHE.HasteBoots.CompressionContinuation.candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionContinuation.candidate

/-- info: 'FormalProof4FHE.HasteBoots.CompressionContinuation.sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionContinuation.sources

/-- info: 'FormalProof4FHE.HasteBoots.CompressionContinuation.test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionContinuation.test

/-- info: 'FormalProof4FHE.HasteBoots.CompressionContinuation.kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionContinuation.kernel

/-- info: 'FormalProof4FHE.HasteBoots.CompressionContinuation.event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionContinuation.event

/-- info: 'FormalProof4FHE.HasteBoots.CompressionContinuation.lifetime_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionContinuation.lifetime_event

/-- info: 'FormalProof4FHE.HasteBoots.CompressionContinuation.private_class_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionContinuation.private_class_monotone

/-- info: 'FormalProof4FHE.HasteBoots.CompressionContinuation.private_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CompressionContinuation.private_monotone

/-- info: 'FormalProof4FHE.HasteBoots.CallerCompressionClassRecovery.covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CallerCompressionClassRecovery.covered

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinCompressionClassProbability.Event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinCompressionClassProbability.Event

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinCompressionClassProbability.Bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinCompressionClassProbability.Bad

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinCompressionClassProbability.prefix_safe_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinCompressionClassProbability.prefix_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinCompressionClassProbability.safe_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinCompressionClassProbability.safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinCompressionClassProbability.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinCompressionClassProbability.bound

/-- info: '_private.FormalProof4FHETest.HasteBootsRefinedCompressionSmoke.0.HasteBootsRefinedCompressionSmoke.first_input_not_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsRefinedCompressionSmoke.first_input_not_parent

/-- info: '_private.FormalProof4FHETest.HasteBootsRefinedCompressionSmoke.0.HasteBootsRefinedCompressionSmoke.rejected_offsets_not_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsRefinedCompressionSmoke.rejected_offsets_not_parent

/-- info: '_private.FormalProof4FHETest.HasteBootsRefinedCompressionSmoke.0.HasteBootsRefinedCompressionSmoke.suspension_preserves_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsRefinedCompressionSmoke.suspension_preserves_input

/-- info: '_private.FormalProof4FHETest.HasteBootsRefinedCompressionSmoke.0.HasteBootsRefinedCompressionSmoke.receipt_input_apart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsRefinedCompressionSmoke.receipt_input_apart

/-- info: '_private.FormalProof4FHETest.HasteBootsRefinedCompressionSmoke.0.HasteBootsRefinedCompressionSmoke.far_read_refinement_unseen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsRefinedCompressionSmoke.far_read_refinement_unseen

/-- info: '_private.FormalProof4FHETest.HasteBootsRefinedCompressionSmoke.0.HasteBootsRefinedCompressionSmoke.parent_recognized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsRefinedCompressionSmoke.parent_recognized
