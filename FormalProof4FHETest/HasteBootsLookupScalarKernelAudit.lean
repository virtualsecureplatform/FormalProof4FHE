module
import all FormalProof4FHE.HasteBoots.LookupCollectorTrace
import all FormalProof4FHE.HasteBoots.LookupScalarKernel
import all FormalProof4FHE.HasteBoots.LookupBatchCollectorTrace
import all FormalProof4FHE.HasteBoots.CallerLookupScalars
import all FormalProof4FHE.HasteBoots.LookupPairChallengeBounds
import all FormalProof4FHETest.HasteBootsLookupScalarKernelSmoke

/-- info: 'FormalProof4FHE.HasteBoots.LookupCollectorTrace.start' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCollectorTrace.start

/-- info: 'FormalProof4FHE.HasteBoots.LookupCollectorTrace.Source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCollectorTrace.Source

/-- info: 'FormalProof4FHE.HasteBoots.LookupCollectorTrace.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCollectorTrace.mono

/-- info: 'FormalProof4FHE.HasteBoots.LookupCollectorTrace.Traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCollectorTrace.Traced

/-- info: 'FormalProof4FHE.HasteBoots.LookupCollectorTrace.traced_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCollectorTrace.traced_mono

/-- info: 'FormalProof4FHE.HasteBoots.LookupCollectorTrace.begin_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCollectorTrace.begin_source

/-- info: 'FormalProof4FHE.HasteBoots.LookupCollectorTrace.collect_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCollectorTrace.collect_source

/-- info: 'FormalProof4FHE.HasteBoots.LookupCollectorTrace.drive_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCollectorTrace.drive_source

/-- info: 'FormalProof4FHE.HasteBoots.LookupCollectorTrace.tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCollectorTrace.tick

/-- info: 'FormalProof4FHE.HasteBoots.LookupCollectorTrace.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCollectorTrace.execute

/-- info: 'FormalProof4FHE.HasteBoots.LookupCollectorTrace.initialized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCollectorTrace.initialized

/-- info: 'FormalProof4FHE.HasteBoots.LookupCollectorTrace.request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCollectorTrace.request

/-- info: 'FormalProof4FHE.HasteBoots.LookupCollectorTrace.source_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCollectorTrace.source_first

/-- info: 'FormalProof4FHE.HasteBoots.LookupScalarKernel.phase' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupScalarKernel.phase

/-- info: 'FormalProof4FHE.HasteBoots.LookupScalarKernel.Event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupScalarKernel.Event

/-- info: 'FormalProof4FHE.HasteBoots.LookupScalarKernel.values_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupScalarKernel.values_congr

/-- info: 'FormalProof4FHE.HasteBoots.LookupScalarKernel.source_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupScalarKernel.source_value

/-- info: 'FormalProof4FHE.HasteBoots.LookupScalarKernel.decoded_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupScalarKernel.decoded_value

/-- info: 'FormalProof4FHE.HasteBoots.LookupScalarKernel.source_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupScalarKernel.source_word

/-- info: 'FormalProof4FHE.HasteBoots.LookupScalarKernel.draw_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupScalarKernel.draw_value

/-- info: 'FormalProof4FHE.HasteBoots.LookupScalarKernel.of_draw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupScalarKernel.of_draw

/-- info: 'FormalProof4FHE.HasteBoots.LookupScalarKernel.conditional_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupScalarKernel.conditional_bound

/-- info: 'FormalProof4FHE.HasteBoots.LookupBatchCollectorTrace.Batch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupBatchCollectorTrace.Batch

/-- info: 'FormalProof4FHE.HasteBoots.LookupBatchCollectorTrace.after_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupBatchCollectorTrace.after_sample

/-- info: 'FormalProof4FHE.HasteBoots.LookupBatchCollectorTrace.tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupBatchCollectorTrace.tick

/-- info: 'FormalProof4FHE.HasteBoots.LookupBatchCollectorTrace.execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupBatchCollectorTrace.execute

/-- info: 'FormalProof4FHE.HasteBoots.LookupBatchCollectorTrace.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupBatchCollectorTrace.initialized

/-- info: 'FormalProof4FHE.HasteBoots.CallerLookupScalars.producer_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CallerLookupScalars.producer_trace

/-- info: 'FormalProof4FHE.HasteBoots.CallerLookupScalars.endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CallerLookupScalars.endpoints

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairChallengeBounds.Domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupPairChallengeBounds.Domain

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairChallengeBounds.tuple_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupPairChallengeBounds.tuple_family

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairChallengeBounds.reciprocal_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupPairChallengeBounds.reciprocal_root

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairChallengeBounds.passes_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupPairChallengeBounds.passes_root

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairChallengeBounds.reciprocal_passes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupPairChallengeBounds.reciprocal_passes

/-- info: '_private.FormalProof4FHETest.HasteBootsLookupScalarKernelSmoke.0.HasteBootsLookupScalarKernelSmoke.completed_original_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsLookupScalarKernelSmoke.completed_original_pair

/-- info: '_private.FormalProof4FHETest.HasteBootsLookupScalarKernelSmoke.0.HasteBootsLookupScalarKernelSmoke.forbidden_offsets_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsLookupScalarKernelSmoke.forbidden_offsets_retained

/-- info: '_private.FormalProof4FHETest.HasteBootsLookupScalarKernelSmoke.0.HasteBootsLookupScalarKernelSmoke.coefficient_rejection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsLookupScalarKernelSmoke.coefficient_rejection

/-- info: '_private.FormalProof4FHETest.HasteBootsLookupScalarKernelSmoke.0.HasteBootsLookupScalarKernelSmoke.retained_inputs_exposed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsLookupScalarKernelSmoke.retained_inputs_exposed

/-- info: '_private.FormalProof4FHETest.HasteBootsLookupScalarKernelSmoke.0.HasteBootsLookupScalarKernelSmoke.retry_inputs_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsLookupScalarKernelSmoke.retry_inputs_distinct

/-- info: '_private.FormalProof4FHETest.HasteBootsLookupScalarKernelSmoke.0.HasteBootsLookupScalarKernelSmoke.genuine_compression_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsLookupScalarKernelSmoke.genuine_compression_collision
