module
import all FormalProof4FHE.HasteBoots.HelperRootsBoundary
import all FormalProof4FHE.HasteBoots.EqualityLookupReceiptView
import all FormalProof4FHE.HasteBoots.EqualityLookupFactorFixation
import all FormalProof4FHE.HasteBoots.OriginalEqualityLookupFactors
import all FormalProof4FHE.HasteBoots.ProgramEqualityLookupFactors
import all FormalProof4FHE.HasteBoots.LoggedEqualityLookupFactors
import all FormalProof4FHE.HasteBoots.EqualityFactorCandidate
import all FormalProof4FHETest.HasteBootsEqualityFactorSmoke

/-- info: 'FormalProof4FHE.HasteBoots.HelperRootsBoundary.readFrames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HelperRootsBoundary.readFrames

/-- info: 'FormalProof4FHE.HasteBoots.HelperRootsBoundary.parse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HelperRootsBoundary.parse

/-- info: 'FormalProof4FHE.HasteBoots.HelperRootsBoundary.read_clean' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HelperRootsBoundary.read_clean

/-- info: 'FormalProof4FHE.HasteBoots.HelperRootsBoundary.native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HelperRootsBoundary.native

/-- info: 'FormalProof4FHE.HasteBoots.HelperRootsBoundary.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HelperRootsBoundary.bound

/-- info: 'FormalProof4FHE.HasteBoots.HelperRootsBoundary.preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HelperRootsBoundary.preserved

/-- info: 'FormalProof4FHE.HasteBoots.HelperRootsBoundary.read_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HelperRootsBoundary.read_sound

/-- info: 'FormalProof4FHE.HasteBoots.HelperRootsBoundary.sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HelperRootsBoundary.sound

/-- info: 'FormalProof4FHE.HasteBoots.EqualityLookupReceiptView.View' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityLookupReceiptView.View

/-- info: 'FormalProof4FHE.HasteBoots.EqualityLookupReceiptView.compare' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityLookupReceiptView.compare

/-- info: 'FormalProof4FHE.HasteBoots.EqualityLookupReceiptView.recover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityLookupReceiptView.recover

/-- info: 'FormalProof4FHE.HasteBoots.EqualityLookupFactorFixation.Side' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityLookupFactorFixation.Side

/-- info: 'FormalProof4FHE.HasteBoots.EqualityLookupFactorFixation.receiptAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityLookupFactorFixation.receiptAt

/-- info: 'FormalProof4FHE.HasteBoots.EqualityLookupFactorFixation.Scalar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityLookupFactorFixation.Scalar

/-- info: 'FormalProof4FHE.HasteBoots.EqualityLookupFactorFixation.receipt_equal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityLookupFactorFixation.receipt_equal

/-- info: 'FormalProof4FHE.HasteBoots.EqualityLookupFactorFixation.coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityLookupFactorFixation.coefficients

/-- info: 'FormalProof4FHE.HasteBoots.EqualityLookupFactorFixation.scalar_on_fiber' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityLookupFactorFixation.scalar_on_fiber

/-- info: 'FormalProof4FHE.HasteBoots.OriginalEqualityLookupFactors.scalars' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OriginalEqualityLookupFactors.scalars

/-- info: 'FormalProof4FHE.HasteBoots.OriginalEqualityLookupFactors.recover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OriginalEqualityLookupFactors.recover

/-- info: 'FormalProof4FHE.HasteBoots.ProgramEqualityLookupFactors.Observed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ProgramEqualityLookupFactors.Observed

/-- info: 'FormalProof4FHE.HasteBoots.ProgramEqualityLookupFactors.in_prelude' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ProgramEqualityLookupFactors.in_prelude

/-- info: 'FormalProof4FHE.HasteBoots.ProgramEqualityLookupFactors.in_reader' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ProgramEqualityLookupFactors.in_reader

/-- info: 'FormalProof4FHE.HasteBoots.ProgramEqualityLookupFactors.input_apart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ProgramEqualityLookupFactors.input_apart

/-- info: 'FormalProof4FHE.HasteBoots.ProgramEqualityLookupFactors.named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ProgramEqualityLookupFactors.named

/-- info: 'FormalProof4FHE.HasteBoots.ProgramEqualityLookupFactors.scalar_on_fiber' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ProgramEqualityLookupFactors.scalar_on_fiber

/-- info: 'FormalProof4FHE.HasteBoots.LoggedEqualityLookupFactors.recover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LoggedEqualityLookupFactors.recover

/-- info: 'FormalProof4FHE.HasteBoots.EqualityFactorCandidate.At' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityFactorCandidate.At

/-- info: 'FormalProof4FHE.HasteBoots.EqualityFactorCandidate.At.reindex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityFactorCandidate.At.reindex

/-- info: 'FormalProof4FHE.HasteBoots.EqualityFactorCandidate.at_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityFactorCandidate.at_fixed

/-- info: 'FormalProof4FHE.HasteBoots.EqualityFactorCandidate.Candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityFactorCandidate.Candidate

/-- info: 'FormalProof4FHE.HasteBoots.EqualityFactorCandidate.attach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityFactorCandidate.attach

/-- info: 'FormalProof4FHE.HasteBoots.EqualityFactorCandidate.fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityFactorCandidate.fixed

/-- info: '_private.FormalProof4FHETest.HasteBootsEqualityFactorSmoke.0.HasteBootsEqualityFactorSmoke.before' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsEqualityFactorSmoke.before

/-- info: '_private.FormalProof4FHETest.HasteBootsEqualityFactorSmoke.0.HasteBootsEqualityFactorSmoke.first_original_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsEqualityFactorSmoke.first_original_boundary

/-- info: '_private.FormalProof4FHETest.HasteBootsEqualityFactorSmoke.0.HasteBootsEqualityFactorSmoke.second_original_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsEqualityFactorSmoke.second_original_boundary

/-- info: '_private.FormalProof4FHETest.HasteBootsEqualityFactorSmoke.0.HasteBootsEqualityFactorSmoke.latest_binder_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsEqualityFactorSmoke.latest_binder_boundary

/-- info: '_private.FormalProof4FHETest.HasteBootsEqualityFactorSmoke.0.HasteBootsEqualityFactorSmoke.bound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsEqualityFactorSmoke.bound

/-- info: '_private.FormalProof4FHETest.HasteBootsEqualityFactorSmoke.0.HasteBootsEqualityFactorSmoke.malformed_latest_rejected' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsEqualityFactorSmoke.malformed_latest_rejected

/-- info: '_private.FormalProof4FHETest.HasteBootsEqualityFactorSmoke.0.HasteBootsEqualityFactorSmoke.receipt_kind_not_binder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsEqualityFactorSmoke.receipt_kind_not_binder
