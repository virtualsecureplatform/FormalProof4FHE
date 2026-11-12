module
import all FormalProof4FHE.HasteBoots.GoldEqualityPointLaw
import all FormalProof4FHE.HasteBoots.EqualityCollectorTrace
import all FormalProof4FHE.HasteBoots.LookupEqualityExposure
import all FormalProof4FHE.HasteBoots.LookupEqualityResidual
import all FormalProof4FHETest.HasteBootsGoldEqualityPointSmoke

/-- info: 'FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.coordinates

/-- info: 'FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.assemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.assemble

/-- info: 'FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.assemble_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.assemble_apply

/-- info: 'FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.uniform_assembly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.uniform_assembly

/-- info: 'FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.values

/-- info: 'FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.conditional_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.conditional_uniform

/-- info: 'FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.eventual_le_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.eventual_le_uniform

/-- info: 'FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.eventual_residual_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.eventual_residual_bound

/-- info: 'FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.completed_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldEqualityPointLaw.completed_values

/-- info: 'FormalProof4FHE.HasteBoots.EqualityCollectorTrace.start' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityCollectorTrace.start

/-- info: 'FormalProof4FHE.HasteBoots.EqualityCollectorTrace.Source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityCollectorTrace.Source

/-- info: 'FormalProof4FHE.HasteBoots.EqualityCollectorTrace.Traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityCollectorTrace.Traced

/-- info: 'FormalProof4FHE.HasteBoots.EqualityCollectorTrace.begin_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityCollectorTrace.begin_source

/-- info: 'FormalProof4FHE.HasteBoots.EqualityCollectorTrace.collect_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityCollectorTrace.collect_source

/-- info: 'FormalProof4FHE.HasteBoots.EqualityCollectorTrace.drive_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityCollectorTrace.drive_source

/-- info: 'FormalProof4FHE.HasteBoots.EqualityCollectorTrace.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityCollectorTrace.initial

/-- info: 'FormalProof4FHE.HasteBoots.EqualityCollectorTrace.tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityCollectorTrace.tick

/-- info: 'FormalProof4FHE.HasteBoots.EqualityCollectorTrace.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityCollectorTrace.execute

/-- info: 'FormalProof4FHE.HasteBoots.EqualityCollectorTrace.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityCollectorTrace.initialized

/-- info: 'FormalProof4FHE.HasteBoots.EqualityCollectorTrace.draw_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityCollectorTrace.draw_value

/-- info: 'FormalProof4FHE.HasteBoots.EqualityCollectorTrace.draw_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityCollectorTrace.draw_point

/-- info: 'FormalProof4FHE.HasteBoots.LookupEqualityExposure.original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupEqualityExposure.original

/-- info: 'FormalProof4FHE.HasteBoots.LookupEqualityResidual.weighted_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupEqualityResidual.weighted_transport

/-- info: 'FormalProof4FHE.HasteBoots.LookupEqualityResidual.nonzero_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupEqualityResidual.nonzero_transport

/-- info: 'FormalProof4FHE.HasteBoots.LookupEqualityResidual.residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupEqualityResidual.residual

/-- info: 'FormalProof4FHE.HasteBoots.LookupEqualityResidual.miss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupEqualityResidual.miss

/-- info: 'FormalProof4FHE.HasteBoots.LookupEqualityResidual.Event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupEqualityResidual.Event

/-- info: 'FormalProof4FHE.HasteBoots.LookupEqualityResidual.of_miss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupEqualityResidual.of_miss

/-- info: 'FormalProof4FHE.HasteBoots.LookupEqualityResidual.conditional_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupEqualityResidual.conditional_bound

/-- info: '_private.FormalProof4FHETest.HasteBootsGoldEqualityPointSmoke.0.HasteBootsGoldEqualityPointSmoke.phase' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsGoldEqualityPointSmoke.phase

/-- info: '_private.FormalProof4FHETest.HasteBootsGoldEqualityPointSmoke.0.HasteBootsGoldEqualityPointSmoke.first_triple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsGoldEqualityPointSmoke.first_triple

/-- info: '_private.FormalProof4FHETest.HasteBootsGoldEqualityPointSmoke.0.HasteBootsGoldEqualityPointSmoke.second_triple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsGoldEqualityPointSmoke.second_triple

/-- info: '_private.FormalProof4FHETest.HasteBootsGoldEqualityPointSmoke.0.HasteBootsGoldEqualityPointSmoke.partial_vector_suspended' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsGoldEqualityPointSmoke.partial_vector_suspended

/-- info: '_private.FormalProof4FHETest.HasteBootsGoldEqualityPointSmoke.0.HasteBootsGoldEqualityPointSmoke.rejected_vector_suspended' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsGoldEqualityPointSmoke.rejected_vector_suspended

/-- info: '_private.FormalProof4FHETest.HasteBootsGoldEqualityPointSmoke.0.HasteBootsGoldEqualityPointSmoke.zero_vector_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsGoldEqualityPointSmoke.zero_vector_complete

/-- info: '_private.FormalProof4FHETest.HasteBootsGoldEqualityPointSmoke.0.HasteBootsGoldEqualityPointSmoke.equality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsGoldEqualityPointSmoke.equality

/-- info: '_private.FormalProof4FHETest.HasteBootsGoldEqualityPointSmoke.0.HasteBootsGoldEqualityPointSmoke.both_points_completed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsGoldEqualityPointSmoke.both_points_completed

/-- info: '_private.FormalProof4FHETest.HasteBootsGoldEqualityPointSmoke.0.HasteBootsGoldEqualityPointSmoke.distinct_original_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsGoldEqualityPointSmoke.distinct_original_inputs
