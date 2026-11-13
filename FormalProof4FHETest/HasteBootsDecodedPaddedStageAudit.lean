module
import all FormalProof4FHE.HasteBoots.PackedCipherSource
import all FormalProof4FHE.HasteBoots.DecodedPaddedNTT
import all FormalProof4FHE.HasteBoots.DecodedPaddedExtraction

/-- info: 'FormalProof4FHE.HasteBoots.PackedCipherSource.transport_cancel' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedCipherSource.transport_cancel

/-- info: 'FormalProof4FHE.HasteBoots.PackedCipherSource.point_surjective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedCipherSource.point_surjective

/-- info: 'FormalProof4FHE.HasteBoots.PackedCipherSource.pack_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedCipherSource.pack_point

/-- info: 'FormalProof4FHE.HasteBoots.PackedCipherSource.unpack_pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedCipherSource.unpack_pack

/-- info: 'FormalProof4FHE.HasteBoots.PackedCipherSource.pack_unpack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedCipherSource.pack_unpack

/-- info: 'FormalProof4FHE.HasteBoots.PackedCipherSource.join_append' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedCipherSource.join_append

/-- info: 'FormalProof4FHE.HasteBoots.PackedCipherSource.ntt_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedCipherSource.ntt_rows

/-- info: 'FormalProof4FHE.HasteBoots.PackedCipherSource.pack_ofRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedCipherSource.pack_ofRows

/-- info: 'FormalProof4FHE.HasteBoots.PackedCipherSource.rows_ofRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedCipherSource.rows_ofRows

/-- info: 'FormalProof4FHE.HasteBoots.PackedCipherSource.flatten_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedCipherSource.flatten_rows

/-- info: 'FormalProof4FHE.HasteBoots.PackedCipherSource.pack_familyCipher' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedCipherSource.pack_familyCipher

/-- info: 'FormalProof4FHE.HasteBoots.PackedCipherSource.ofRows_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedCipherSource.ofRows_family

/-- info: 'FormalProof4FHE.HasteBoots.PackedCipherSource.family_ntt_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedCipherSource.family_ntt_rows

/-- info: 'FormalProof4FHE.HasteBoots.PackedCipherSource.equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedCipherSource.equivalence

/-- info: 'FormalProof4FHE.HasteBoots.DecodedPaddedNTT.relation_of_not_risk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DecodedPaddedNTT.relation_of_not_risk

/-- info: 'FormalProof4FHE.HasteBoots.DecodedPaddedNTT.native_transform_of_not_risk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DecodedPaddedNTT.native_transform_of_not_risk

/-- info: 'FormalProof4FHE.HasteBoots.DecodedPaddedNTT.cipher_family_eq_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DecodedPaddedNTT.cipher_family_eq_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.DecodedPaddedExtraction.source_eq_pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DecodedPaddedExtraction.source_eq_pack

/-- info: 'FormalProof4FHE.HasteBoots.DecodedPaddedExtraction.wrong_implies_risk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DecodedPaddedExtraction.wrong_implies_risk

/-- info: 'FormalProof4FHE.HasteBoots.DecodedPaddedExtraction.extraction_of_not_risk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DecodedPaddedExtraction.extraction_of_not_risk

/-- info: 'FormalProof4FHE.HasteBoots.DecodedPaddedExtraction.increment_family_eq_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DecodedPaddedExtraction.increment_family_eq_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.DecodedPaddedExtraction.semantic_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DecodedPaddedExtraction.semantic_safe_bound
