module
import all FormalProof4FHE.HasteBoots.RecordedFamilyEmbedding
import all FormalProof4FHE.HasteBoots.DecodedEvaluationKey
import all FormalProof4FHE.HasteBoots.ExecutedReconstructionCommonFamily
import all FormalProof4FHE.HasteBoots.ExecutedProductCommonFamily
import all FormalProof4FHE.HasteBoots.ExecutedNTTCommonFamily
import all FormalProof4FHE.HasteBoots.ExecutedKnownInputCommonFamily
import all FormalProof4FHE.HasteBoots.RectangularEvaluationKeySwitch

/-- info: 'FormalProof4FHE.HasteBoots.RecordedFamilyEmbedding.logical_eq_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RecordedFamilyEmbedding.logical_eq_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.RecordedFamilyEmbedding.cipher_eq_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RecordedFamilyEmbedding.cipher_eq_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.DecodedEvaluationKey.transformEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DecodedEvaluationKey.transformEquiv

/-- info: 'FormalProof4FHE.HasteBoots.DecodedEvaluationKey.inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DecodedEvaluationKey.inverse

/-- info: 'FormalProof4FHE.HasteBoots.DecodedEvaluationKey.transform_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DecodedEvaluationKey.transform_inverse

/-- info: 'FormalProof4FHE.HasteBoots.DecodedEvaluationKey.inverse_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DecodedEvaluationKey.inverse_transform

/-- info: 'FormalProof4FHE.HasteBoots.DecodedEvaluationKey.key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DecodedEvaluationKey.key

/-- info: 'FormalProof4FHE.HasteBoots.DecodedEvaluationKey.key_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DecodedEvaluationKey.key_transform

/-- info: 'FormalProof4FHE.HasteBoots.DecodedEvaluationKey.key_eq_of_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DecodedEvaluationKey.key_eq_of_setup

/-- info: 'FormalProof4FHE.HasteBoots.DecodedEvaluationKey.increment_of_constraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DecodedEvaluationKey.increment_of_constraints

/-- info: 'FormalProof4FHE.HasteBoots.DecodedEvaluationKey.family_increment_of_constraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DecodedEvaluationKey.family_increment_of_constraints

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedReconstructionCommonFamily.relation_on_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedReconstructionCommonFamily.relation_on_world

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedReconstructionCommonFamily.wrong_relation_implies_risk_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedReconstructionCommonFamily.wrong_relation_implies_risk_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedProductCommonFamily.identity_on_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedProductCommonFamily.identity_on_world

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedProductCommonFamily.wrong_identity_implies_risk_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedProductCommonFamily.wrong_identity_implies_risk_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedNTTCommonFamily.selected_cipher' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedNTTCommonFamily.selected_cipher

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedNTTCommonFamily.transform_on_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedNTTCommonFamily.transform_on_world

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedNTTCommonFamily.wrong_transform_implies_risk_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedNTTCommonFamily.wrong_transform_implies_risk_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedKnownInputCommonFamily.negative_mask_on_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedKnownInputCommonFamily.negative_mask_on_world

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedKnownInputCommonFamily.wrong_mask_implies_risk_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedKnownInputCommonFamily.wrong_mask_implies_risk_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.RectangularEvaluationKeySwitch.increment_of_not_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularEvaluationKeySwitch.increment_of_not_false

/-- info: 'FormalProof4FHE.HasteBoots.RectangularEvaluationKeySwitch.wrong_increment_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularEvaluationKeySwitch.wrong_increment_coverage
