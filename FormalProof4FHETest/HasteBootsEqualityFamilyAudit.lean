module
import all FormalProof4FHE.HasteBoots.EqualityInputFamilyView
import all FormalProof4FHE.HasteBoots.AllocatedEqualityParentPrefix
import all FormalProof4FHE.HasteBoots.AllocatedEqualityParentFamily
import all FormalProof4FHE.HasteBoots.EqualityLookupReadStability
import all FormalProof4FHE.HasteBoots.CanonicalEqualityReadStability
import all FormalProof4FHE.HasteBoots.EqualityFamilyCandidate
import all FormalProof4FHETest.HasteBootsEqualityFamilySmoke

/-- info: 'FormalProof4FHE.HasteBoots.EqualityInputFamilyView.forget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityInputFamilyView.forget

/-- info: 'FormalProof4FHE.HasteBoots.EqualityInputFamilyView.recover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityInputFamilyView.recover

/-- info: 'FormalProof4FHE.HasteBoots.EqualityInputFamilyView.parsed_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityInputFamilyView.parsed_root

/-- info: 'FormalProof4FHE.HasteBoots.AllocatedEqualityParentPrefix.known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AllocatedEqualityParentPrefix.known

/-- info: 'FormalProof4FHE.HasteBoots.AllocatedEqualityParentFamily.at_equality_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AllocatedEqualityParentFamily.at_equality_first

/-- info: 'FormalProof4FHE.HasteBoots.AllocatedEqualityParentFamily.with_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AllocatedEqualityParentFamily.with_roots

/-- info: 'FormalProof4FHE.HasteBoots.EqualityLookupReadStability.program_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityLookupReadStability.program_read

/-- info: 'FormalProof4FHE.HasteBoots.EqualityLookupReadStability.allocated_program_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityLookupReadStability.allocated_program_read

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalEqualityReadStability.program_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalEqualityReadStability.program_read

/-- info: 'FormalProof4FHE.HasteBoots.EqualityFamilyCandidate.Candidate' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityFamilyCandidate.Candidate

/-- info: 'FormalProof4FHE.HasteBoots.EqualityFamilyCandidate.sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityFamilyCandidate.sources

/-- info: 'FormalProof4FHE.HasteBoots.EqualityFamilyCandidate.helpers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityFamilyCandidate.helpers

/-- info: 'FormalProof4FHE.HasteBoots.EqualityFamilyCandidate.families_on_fiber' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityFamilyCandidate.families_on_fiber

/-- info: 'FormalProof4FHE.HasteBoots.EqualityFamilyCandidate.recover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityFamilyCandidate.recover

/-- info: 'FormalProof4FHE.HasteBoots.EqualityFamilyCandidate.tables_at_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.EqualityFamilyCandidate.tables_at_first

/-- info: '_private.FormalProof4FHETest.HasteBootsEqualityFamilySmoke.0.HasteBootsEqualityFamilySmoke.originalRoots' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsEqualityFamilySmoke.originalRoots

/-- info: '_private.FormalProof4FHETest.HasteBootsEqualityFamilySmoke.0.HasteBootsEqualityFamilySmoke.first_reader_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsEqualityFamilySmoke.first_reader_roots

/-- info: '_private.FormalProof4FHETest.HasteBootsEqualityFamilySmoke.0.HasteBootsEqualityFamilySmoke.second_reader_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsEqualityFamilySmoke.second_reader_roots

/-- info: '_private.FormalProof4FHETest.HasteBootsEqualityFamilySmoke.0.HasteBootsEqualityFamilySmoke.decoyChild' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsEqualityFamilySmoke.decoyChild

/-- info: '_private.FormalProof4FHETest.HasteBootsEqualityFamilySmoke.0.HasteBootsEqualityFamilySmoke.repeatedRoots' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsEqualityFamilySmoke.repeatedRoots

/-- info: '_private.FormalProof4FHETest.HasteBootsEqualityFamilySmoke.0.HasteBootsEqualityFamilySmoke.repeated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsEqualityFamilySmoke.repeated

/-- info: '_private.FormalProof4FHETest.HasteBootsEqualityFamilySmoke.0.HasteBootsEqualityFamilySmoke.repeated_jobs_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsEqualityFamilySmoke.repeated_jobs_preserved

/-- info: '_private.FormalProof4FHETest.HasteBootsEqualityFamilySmoke.0.HasteBootsEqualityFamilySmoke.decoy_does_not_replace_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsEqualityFamilySmoke.decoy_does_not_replace_roots

/-- info: '_private.FormalProof4FHETest.HasteBootsEqualityFamilySmoke.0.HasteBootsEqualityFamilySmoke.duplicate_roots_still_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsEqualityFamilySmoke.duplicate_roots_still_named
