module
import all FormalProof4FHE.HasteBoots.RecordedSourceWorld
import all FormalProof4FHE.HasteBoots.ExecutedReconstructionWorld
import all FormalProof4FHE.HasteBoots.ExecutedProductWorld
import all FormalProof4FHE.HasteBoots.ExecutedNTTWorld
import all FormalProof4FHE.HasteBoots.ExecutedKnownInputWorld

/-- info: 'FormalProof4FHE.HasteBoots.RecordedSourceWorld.Available' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RecordedSourceWorld.Available

/-- info: 'FormalProof4FHE.HasteBoots.RecordedSourceWorld.Index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RecordedSourceWorld.Index

/-- info: 'FormalProof4FHE.HasteBoots.RecordedSourceWorld.family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RecordedSourceWorld.family

/-- info: 'FormalProof4FHE.HasteBoots.RecordedSourceWorld.recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RecordedSourceWorld.recorded

/-- info: 'FormalProof4FHE.HasteBoots.RecordedSourceWorld.slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RecordedSourceWorld.slot

/-- info: 'FormalProof4FHE.HasteBoots.RecordedSourceWorld.slot_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RecordedSourceWorld.slot_eq

/-- info: 'FormalProof4FHE.HasteBoots.RecordedSourceWorld.logical_eq_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RecordedSourceWorld.logical_eq_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.RecordedSourceWorld.cipher_eq_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RecordedSourceWorld.cipher_eq_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedReconstructionWorld.relation_or_risk_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedReconstructionWorld.relation_or_risk_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedProductWorld.identity_or_risk_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedProductWorld.identity_or_risk_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedNTTWorld.transform_or_risk_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedNTTWorld.transform_or_risk_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedKnownInputWorld.slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedKnownInputWorld.slot

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedKnownInputWorld.negative_mask_or_risk_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedKnownInputWorld.negative_mask_or_risk_or_bad
